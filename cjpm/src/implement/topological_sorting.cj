// Copyright (c) Huawei Technologies Co., Ltd. 2025. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
//
// See https://cangjie-lang.cn/pages/LICENSE for license information.

package cjpm.implement

import std.collection.*
import std.sort.*
import cjpm.config.*

// Topological sorting by BFS.
func topoSort(topoData: DepModel): Bool {
    for (pkgName in topoData.binaryPkgList.keys()) {
        if (!topoData.packageDepMap.contains(pkgName)) {
            topoData.packageDepMap[pkgName] = ResolveItem()
        }
    }

    let numModules = topoData.getLen()
    if (numModules == 0) {
        return true
    }

    topoData.forEach(
        {
            name: String, indegrees: HashMap<String, Int64>, outdegrees: HashMap<String, Int64>, edges: HashMap<String,
            ArrayList<String>> =>
            indegrees[name] = 0 // Setting default values for maps to prevent nil exceptions.
            topoData.forEachDependency(
                name,
                {
                    depName: String =>
                    indegrees[name] += 1 // Record indegree.
                    if (!outdegrees.contains(name)) {
                        outdegrees[name] = 0
                    }
                    if (edges.contains(depName)) {
                        edges[depName].add(name)
                        outdegrees[depName] += 1
                    } else {
                        edges[depName] = ArrayList<String>([name])
                        outdegrees[depName] = 1
                    }
                    return
                }
            )
            return
        }
    )

    if (!lackPackageCheck(topoData)) {
        return false
    }

    // If there are nodes left unprocessed, a cycle exists among the module's packages. Rather than
    // rejecting it (as before), condense each cycle into a strongly-connected component (SCC): the
    // compiler can compile a group of mutually-dependent source packages together in one invocation.
    dependencyAnalysis(topoData)
    if (topoData.readyPkgs.size != numModules) {
        reverseEdges(topoData)
        if (!condenseSccsAndReorder(topoData)) {
            outDegreeAnalysis(topoData)
            printCyclicDependency(topoData)
            return false
        }
    }

    // Check that a combined (super) package is not imported by its own sub packages. `edges` may still
    // contain cycles here (they were condensed into SCCs above rather than rejected), so this must not
    // assume an acyclic graph; `checkSubPkgDep` tolerates cycles via its `usedPkg` visited guard.
    for (superPkgName in topoData.superPkgMap.keys()) {
        let usedPkg = HashSet<String>()
        for (subPkg in topoData.edges.get(superPkgName) ?? ArrayList<String>()) {
            if (!checkSubPkgDep(superPkgName, topoData.edges, subPkg, usedPkg)) {
                return false
            }
        }
    }

    retainSourceCodePkg(topoData)
    return true
}

// Check sub-package-dep for super package
func checkSubPkgDep(superPkg: String, edges: HashMap<String, ArrayList<String>>, curPkg: String,
    usedPkg: HashSet<String>): Bool {
    usedPkg.add(curPkg)
    if (superPkg == curPkg.split(".")[0]) {
        eprintln("Error: combined package '${superPkg}' is depended (directly or indirectly) " +
            "by its sub package '${curPkg}', cannot combine it")
        return false
    }
    for (subPkg in edges.get(curPkg) ?? ArrayList<String>()) {
        if (!usedPkg.contains(subPkg) && !checkSubPkgDep(superPkg, edges, subPkg, usedPkg)) {
            return false
        }
    }
    return true
}

// Delete redundant packages from readyPkgs
func retainSourceCodePkg(topoData: DepModel): Unit {
    var res = ArrayList<String>()
    for (pkg in topoData.readyPkgs) {
        if (topoData.sourceCodePkgList.contains(pkg)) {
            res.add(pkg)
        }
    }
    topoData.readyPkgs = res
    return
}

// Kosaraju pass 1: DFS on `edges` (dependency -> dependent), append nodes in finish order.
func sccDfs1(topoData: DepModel, u: String, visited: HashSet<String>, finishOrder: ArrayList<String>): Unit {
    visited.add(u)
    for (v in topoData.edges.get(u) ?? ArrayList<String>()) {
        if (!visited.contains(v)) {
            sccDfs1(topoData, v, visited, finishOrder)
        }
    }
    finishOrder.add(u)
    return
}

// Kosaraju pass 2: DFS on `reverseEdges` (dependent -> dependency), assign SCC id.
func sccDfs2(topoData: DepModel, u: String, id: Int64, sccIdOf: HashMap<String, Int64>): Unit {
    sccIdOf[u] = id
    for (v in topoData.reverseEdges.get(u) ?? ArrayList<String>()) {
        if (!sccIdOf.contains(v)) {
            sccDfs2(topoData, v, id, sccIdOf)
        }
    }
    return
}

// Detect strongly-connected components among the (cyclic) packages and rebuild `readyPkgs` as a valid
// build order in which every multi-member SCC is represented by a single leader package. The members of
// each cyclic SCC are recorded in `sccGroups` so the build compiles them together with one
// `cjc -p <m1> -p <m2> ...` invocation. Returns false if the condensation is somehow still cyclic.
func condenseSccsAndReorder(topoData: DepModel): Bool {
    let nodes = ArrayList<String>()
    for ((name, _) in topoData.indegrees) {
        nodes.add(name)
    }
    sort(nodes, by: cmpStr, stable: true)

    // Kosaraju.
    let visited = HashSet<String>()
    let finishOrder = ArrayList<String>()
    for (n in nodes) {
        if (!visited.contains(n)) {
            sccDfs1(topoData, n, visited, finishOrder)
        }
    }
    let sccIdOf = HashMap<String, Int64>()
    var sccCount: Int64 = 0
    var idx = finishOrder.size - 1
    while (idx >= 0) {
        let n = finishOrder[idx]
        if (!sccIdOf.contains(n)) {
            sccDfs2(topoData, n, sccCount, sccIdOf)
            sccCount += 1
        }
        idx -= 1
    }

    // Group nodes per SCC and choose a deterministic leader (prefer a source package).
    let sccMembers = HashMap<Int64, ArrayList<String>>()
    for (n in nodes) {
        let id = sccIdOf[n]
        if (!sccMembers.contains(id)) {
            sccMembers[id] = ArrayList<String>()
        }
        sccMembers[id].add(n)
    }
    let leaderOf = HashMap<Int64, String>()
    for ((id, members) in sccMembers) {
        sort(members, by: cmpStr, stable: true)
        var leader = members[0]
        for (m in members) {
            if (topoData.sourceCodePkgList.contains(m)) {
                leader = m
                break
            }
        }
        leaderOf[id] = leader
        if (members.size > 1) {
            let group = ArrayList<String>()
            for (m in members) {
                group.add(m)
                topoData.pkgToSccLeader[m] = leader
            }
            topoData.sccGroups[leader] = group
        }
    }

    // Build the condensation graph (SCC -> SCC) and Kahn-sort it (dependency SCC first).
    let sccEdges = HashMap<Int64, ArrayList<Int64>>()
    let sccIndeg = HashMap<Int64, Int64>()
    for ((id, _) in sccMembers) {
        sccIndeg[id] = 0
    }
    let seenEdge = HashSet<String>()
    for ((u, dependents) in topoData.edges) {
        if (!sccIdOf.contains(u)) {
            continue
        }
        let su = sccIdOf[u]
        for (v in dependents) {
            if (!sccIdOf.contains(v)) {
                continue
            }
            let sv = sccIdOf[v]
            if (su == sv) {
                continue
            }
            let key = "${su}->${sv}"
            if (seenEdge.contains(key)) {
                continue
            }
            seenEdge.add(key)
            if (!sccEdges.contains(su)) {
                sccEdges[su] = ArrayList<Int64>()
            }
            sccEdges[su].add(sv)
            sccIndeg[sv] += 1
        }
    }

    let queue = ArrayList<Int64>()
    for ((id, d) in sccIndeg) {
        if (d == 0) {
            queue.add(id)
        }
    }
    let orderedSccs = ArrayList<Int64>()
    while (queue.size != 0) {
        sort(queue, by: {a: Int64, b: Int64 => leaderOf[a].compare(leaderOf[b])}, stable: true)
        let cur = queue[0]
        queue.remove(at: 0)
        orderedSccs.add(cur)
        for (w in sccEdges.get(cur) ?? ArrayList<Int64>()) {
            sccIndeg[w] -= 1
            if (sccIndeg[w] == 0) {
                queue.add(w)
            }
        }
    }
    if (orderedSccs.size != sccMembers.size) {
        return false
    }

    // Emit one leader per SCC, in dependency-first order.
    let newReady = ArrayList<String>()
    for (id in orderedSccs) {
        newReady.add(leaderOf[id])
    }
    topoData.readyPkgs = newReady
    return true
}

// Check the missing packages
func lackPackageCheck(topoData: DepModel) {
    var lackPackage = ArrayList<String>()
    for ((packageName, _) in topoData.edges) {
        if (!topoData.sourceCodePkgList.contains(packageName) && !topoData.binaryPkgList.contains(packageName)) {
            lackPackage.add(packageName)
        }
    }
    if (lackPackage.size != 0) {
        eprintln("Error: can not find the following dependencies")
        for (packageName in lackPackage) {
            eprintln("    ${packageName}")
        }
        return false
    }
    return true
}

func dependencyAnalysis(topoData: DepModel): Unit {
    // Queue all nodes with zero indegree.
    var queue = ArrayList<String>()
    for ((i, _) in topoData.indegrees) {
        if (topoData.indegrees[i] == 0) {
            queue.add(i)
        }
    }
    sort(queue, by: cmpStr, stable: true)

    var curQueue = ArrayList<String>()

    // Loop processing all queue.
    while (queue.size != 0) {
        var cur = queue[0]
        queue.remove(at: 0)
        topoData.readyPkgs.add(cur)

        if (!topoData.edges.contains(cur)) {
            if (queue.size == 0 && curQueue.size != 0) {
                queue.add(all: curQueue)
                sort(queue, by: cmpStr, stable: true)
                curQueue.clear()
            }
            continue
        }

        // Dealing with subsequent nodes of that node.
        for (v in topoData.edges[cur]) {
            if (!topoData.indegrees.contains(v)) {
                continue
            }
            topoData.indegrees[v] -= 1
            topoData.outdegrees[cur] -= 1
            if (topoData.indegrees[v] == 0) {
                curQueue.add(v)
            }
        }

        if (queue.size == 0 && curQueue.size != 0) {
            queue.add(all: curQueue)
            sort(queue, by: cmpStr, stable: true)
            curQueue.clear()
        }
    }

    return
}

func cmpStr(str1: String, str2: String): Ordering {
    return str1.compare(str2)
}

func reverseEdges(topoData: DepModel): Unit {
    topoData.reverseEdges = HashMap<String, ArrayList<String>>()
    for ((src, dstList) in topoData.edges) {
        for (dst in dstList) {
            if (!topoData.reverseEdges.contains(dst)) {
                topoData.reverseEdges.add(dst, ArrayList<String>([src]))
            } else {
                topoData.reverseEdges[dst].add(src)
            }
        }
    }
}

func outDegreeAnalysis(topoData: DepModel): Unit {
    // Queue all nodes with zero outdegree.
    var queue = ArrayList<String>()
    for ((i, _) in topoData.outdegrees) {
        if (topoData.outdegrees[i] == 0 && !topoData.readyPkgs.contains(i)) {
            queue.add(i)
        }
    }
    sort(queue, by: cmpStr, stable: true)

    var curQueue = ArrayList<String>()

    // Loop processing all queue.
    while (queue.size != 0) {
        var cur = queue[0]
        queue.remove(at: 0)
        topoData.readyPkgs.add(cur)

        if (!topoData.reverseEdges.contains(cur)) {
            if (queue.size == 0 && curQueue.size != 0) {
                queue.add(all: curQueue)
                sort(queue, by: cmpStr, stable: true)
                curQueue.clear()
            }
            continue
        }

        // Dealing with presequent nodes of that node.
        for (v in topoData.reverseEdges[cur]) {
            if (!topoData.outdegrees.contains(v)) {
                continue
            }
            topoData.indegrees[cur] -= 1
            topoData.outdegrees[v] -= 1
            if (topoData.outdegrees[v] == 0 && !topoData.readyPkgs.contains(v)) {
                curQueue.add(v)
            }
        }

        if (queue.size == 0 && curQueue.size != 0) {
            queue.add(all: curQueue)
            sort(queue, by: cmpStr, stable: true)
            curQueue.clear()
        }
    }
}

func printCyclicDependency(topoData: DepModel): Unit {
    for ((fullName, _) in topoData.edges) {
        var cyclicList = ArrayList<String>()
        let start = fullName
        cyclicSearch(fullName, cyclicList, start, topoData)
        topoData.visit.add(fullName)
    }
    return
}

func cyclicSearch(fullName: String, cyclicList: ArrayList<String>, start: String, topoData: DepModel): Unit {
    if (topoData.readyPkgs.contains(fullName) || topoData.visit.contains(fullName)) {
        return
    }

    if (cyclicList.contains(fullName)) {
        if (fullName == start) {
            cyclicPrint(cyclicList, topoData)
        }
        return
    }

    if (!topoData.edges.contains(fullName)) {
        return
    }

    let index = cyclicList.size
    cyclicList.add(fullName)
    for (pkg in topoData.edges[fullName]) {
        cyclicSearch(pkg, cyclicList, start, topoData)
    }
    cyclicList.remove(at: index)
    return
}

func cyclicPrint(cyclicList: ArrayList<String>, topoData: DepModel): Unit {
    if (cyclicList.size == 0) {
        return
    }
    eprintln("cyclic dependency:")
    var size = cyclicList.size
    for (i in size - 1..=0 : -1) {
        var prePackage: String = cyclicList[i]
        var nextPackage: String = ""
        if (i + 1 == size) {
            nextPackage = cyclicList[0]
        } else {
            nextPackage = cyclicList[i + 1]
        }
        var combinedStr = ""
        if (topoData.superPkgMap.contains(nextPackage) && topoData.superPkgMap.contains(prePackage)) {
            combinedStr = "(between combined modules)"
        } else if (topoData.superPkgMap.contains(nextPackage) &&
            topoData.packageDepMap[nextPackage].forcedRequires.contains(prePackage)) {
            combinedStr = "(because of combined module '${nextPackage}')"
        }
        eprintln("${nextPackage} -> ${prePackage}${combinedStr}")
    }
    eprint("\n")
}

// Get valid order for package requires.
func packageReruiresSort(pkgMap: HashMap<String, RequiresPackagesInfo>): BinDeps {
    if (pkgMap.isEmpty()) {
        return BinDeps()
    }

    // Record all dependency in edges.
    var edges = getPackageRequireDependency(pkgMap)

    var queue = ArrayList<String>()
    for ((p, cnt) in edges) {
        if (cnt == 0) {
            queue.add(p)
        }
    }

    let pkgSort = ArrayList<String>()
    // Loop processing all queue.
    while (queue.size != 0) {
        sort(queue, by: cmpStr, stable: true)
        let cur = queue[0]
        queue.remove(at: 0)
        pkgSort.add(cur)
        // Dealing with subsequent nodes of cur node.
        for ((k, v) in pkgMap) {
            if (!v.requires.contains(cur)) {
                continue
            }
            edges[k] -= 1
            if (edges[k] == 0) {
                queue.add(k)
            }
        }
    }

    let binDeps = BinDeps()
    for (fullName in pkgSort) {
        if (!pkgMap.contains(fullName)) {
            continue
        }
        binDeps.packageRequiresSort.add(fullName)
    }
    binDeps.packageRequires = HashMap<String, RequiresPackagesInfo>(pkgMap)
    return binDeps
}

func getPackageRequireDependency(pkgMap: HashMap<String, RequiresPackagesInfo>): HashMap<String, Int64> {
    // Record all packages.
    var allPackages = HashSet<String>()
    for ((k, v) in pkgMap) {
        allPackages.add(k)
        allPackages.add(all: v.requires)
    }

    // Record all dependency in edges.
    var edges = HashMap<String, Int64>()
    for (p in allPackages) {
        if (pkgMap.contains(p)) {
            edges[p] = pkgMap[p].requires.size
        } else {
            edges[p] = 0
        }
    }
    return edges
}
