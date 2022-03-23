#!/usr/bin/python

# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from __future__ import print_function

from node import *
from graph import *
from simplify import *
from config import *

import copy

maskingOps = ['^', '+']
bijectiveOps = ['^']


# Strategies:
#  * without retries
#    - always simplify: START_REPLACE
#    - simplify at the start only: START
#    - simplify after replacement only: REPLACE
#    - never simplify: NONE
#  * with retries
#    - always after failure: FAIL
#    - simplify once at the start and then after a failure: START_FAIL
#    - not simplify at the start (retry if failure) but after each replacement and after a failure: FAIL_REPLACE
#  * with full copy
#    - applicable for each strategy above except always simplify, and during the second run, always use simplify
#
# TAGS CONSTRUCTED:
# * START
# * FAILURE
# * REPLACE
#
#                  START    FAILURE     REPLACE
# START_REPLACE    1        X           1
# START            1        0           0
# REPLACE          0        0           1
# NONE             0        0           0
# FAIL             0        1           0
# START_FAIL       1        1           0
# FAIL_REPLACE     0        1           1
#
# FAIL_1 : simplification strategy of algorithm of Barthe et al. MaskVerif: simplify once after failure only
# TAGS values: START = 0, FAILURE = 1, REPLACE = 0
# uses a special TAG SINGLE_REPLACE to differentiate from FAIL to not reset the variable simplifyDone after a replacement





def niOrig(g, copyGraph = True):
    if copyGraph:
        graph = copy.deepcopy(g)
    else:
        graph = g
 
    if simplifyStrategy['FULL_RETRY'] and not copyGraph:
        backupGraph = copy.deepcopy(graph)

    res = niOrigRun(graph, False)
    if res:
        return True

    if simplifyStrategy['FULL_RETRY']:
        if copyGraph:
            # Backup not done, copying the input graph
            backupGraph = copy.deepcopy(g)
        return niOrigRun(backupGraph, True)
    else:
        return False


def niOrigRun(graph, alwaysSimplify):
    assert(graph.roots != None)

    nodeList = graph.roots
    
    if alwaysSimplify or simplifyStrategy['START']:
        #print('# Simplify')
        for n in nodeList:
            simplify(n, nodeList)
            simplifyDone = True
    else:
        simplifyDone = False

    cpt = 0
    while True:
        cpt += 1

        if not graph.secretNodes:
            return True

        singleOccurrenceMasks = set()
        for maskNode in graph.maskNodes:
            if len(maskNode.parents) == 1 and maskNode.parents[0].op in maskingOps:
                singleOccurrenceMasks.add(maskNode)

        if len(singleOccurrenceMasks) == 0:
            # Failure
            #print('# Failure')
            if simplifyDone or not simplifyStrategy['FAILURE']:
                #print('# Return')
                return False
            else:
                #print('# Simplify')
                for n in nodeList:
                    simplify(n, nodeList)
                simplifyDone = True
                continue

        for maskNode in singleOccurrenceMasks:
            n = maskNode
            break
        
        # Resetting the simplifyDone tag since the graph structure will change
        simplifyDone = False

        # Replacing subgraph masked by n
        assert(len(n.parents) == 1)
        opNode = n.parents[0]
        assert(isinstance(opNode, OpNode))

        # Finding the node for which the mask masks the largest expression
        while len(opNode.parents) > 0 and (opNode.parents[0].op in maskingOps or opNode.parents[0].op == '~'):
            opNode = opNode.parents[0]

        #print('# Replacement')
        replaceOpNodeWithMaskNode(opNode, n, nodeList)

        # Simplify
        if alwaysSimplify or simplifyStrategy['REPLACE']:
            #print('# Simplify')
            for n in nodeList:
                simplify(n, nodeList)
                simplifyDone = True
        else:
            simplifyDone = False




def checkNodeInSubExp(n, m):
    # Checks that m is not a (sub-)child of n
    assert(len(m.parents) <= 1)
    i = m
    while i is not n and len(i.parents) != 0:
        assert(len(i.parents) == 1)
        i = i.parents[0]
    return i is n


def computeDepth(n):
    depth = 0
    i = n
    while len(i.parents) != 0:
        depth += 1
        i = i.parents[0]
    return depth


def leafIsInSubExp(m, e):
    if len(e.children) == 0:
        return e is m
    for child in e.children:
        present = leafIsInSubExp(m, child)
        if present:
            return True
    return False


def replaceOpNodeWithMaskNode(opNode, maskNode, nodeList):
    if len(opNode.parents) > 0:
        # the mask is not masking the whole expression
        parentNode = opNode.parents[0]
        # Cannot use remove and append because the index must be kept, in case of non-commutative operators
        idx = 0
        for i in range(len(parentNode.children)):
            if parentNode.children[i] is opNode:
                parentNode.children[i] = maskNode
                break
        maskNode.parents.append(parentNode)
    else:
        # Modify nodeList for putting maskNode instead of opNode
        idx = 0
        while idx < len(nodeList):
            if nodeList[idx] is opNode:
                nodeList[idx] = maskNode
                break
            idx += 1
        
    # Remove links from symbols to OpNodes in replaced expression and deallocate nodes
    opNode.removeSymbRefs(nodeList)




def ni(g, copyGraph = True):
    if copyGraph:
        graph = copy.deepcopy(g)
    else:
        graph = g
 
    if simplifyStrategy['FULL_RETRY'] and not copyGraph:
        backupGraph = copy.deepcopy(graph)

    res = niRun(graph, False)
    if res:
        return True

    if simplifyStrategy['FULL_RETRY']:
        if copyGraph:
            # Backup not done, copying the input graph
            backupGraph = copy.deepcopy(g)
        return niRun(backupGraph, True)
    else:
        return False


def niRun(graph, alwaysSimplify):
    assert(graph.roots != None)

    nodeList = graph.roots

    #for b in range(len(nodeList)):
    #    print('NI bit %d: %s' % (b, nodeList[b]))

    if alwaysSimplify or simplifyStrategy['START']:
        for n in nodeList:
            simplify(n, nodeList)
            simplifyDone = True
    else:
        simplifyDone = False

    #for b in range(len(nodeList)):
    #    print('NI bit %d simplified: %s' % (b, nodeList[b]))

    r = set()
    cpt = 0
    while True:
        #print('# Starting iteration %d' % cpt)
        #nodeList[0].graph.dump('dot/graph_%d.dot' % cpt, False)
        cpt += 1

        if not graph.secretNodes:
            #print('# No more secret...')
            return True

        if not graph.maskNodes:
            # Simplifying cannot add mask Nodes...
            #print('Simplifying cannot add mask Nodes...')
            return False

        # nbMaskOccurrences used later: to have the mask list for each number of occurrence
        nbMaskOccurrences = {}
        singleOccurrenceMaskNode = None
        for maskNode in graph.maskNodes:
            # if maskNode is a "root", we do not take it because it would recomplexify the expression
            if maskNode in nodeList:
                r.add(maskNode)
            if maskNode not in r:
                nbOcc = len(maskNode.parents) # we have nodeList.count(maskNode) == 0
                assert(nbOcc > 0)
                if nbOcc not in nbMaskOccurrences:
                    nbMaskOccurrences[nbOcc] = set()
                #print('# Adding %s to nbMaskOccurrences (%d occurrences)' % (maskNode.symb, nbOcc))
                nbMaskOccurrences[nbOcc].add(maskNode)

                extMaskNode = maskNode
                while len(extMaskNode.parents) > 0 and (extMaskNode.parents[0].op == '-' or extMaskNode.parents[0] == '~'):
                    extMaskNode = extMaskNode.parents[0]
                if nbOcc == 1 and extMaskNode.parents and extMaskNode.parents[0].op in maskingOps:
                    singleOccurrenceMaskNode = maskNode
                    break


        # Optimization (to avoid simplifying all nodes...)
        if singleOccurrenceMaskNode != None:
            maskNode = singleOccurrenceMaskNode
            r.add(maskNode)

            # Replacing subgraph masked by n
            assert(len(maskNode.parents) == 1)
            opNode = extMaskNode.parents[0]
            # We search for a possibly better OpNode to replace
            while len(opNode.parents) > 0 and (opNode.parents[0].op in maskingOps or opNode.parents[0].op == '-' or opNode.parents[0].op == '~'):
                opNode = opNode.parents[0]
            #print('# Replacing %s with single occurrence mask %s' % (opNode, maskNode.symb))
            assert(isinstance(opNode, OpNode))

            replaceOpNodeWithMaskNode(opNode, maskNode, nodeList)
            continue # return to the beginning of the while loop


        # Criteria: Total number of occurrences (# of replacements), and depth
        possibleOpNodes = {}
        for m in graph.maskNodes:
            if m in r:
                continue
            possibleOpNodes[m] = {}
            for i in range(len(m.parents)):
                parent = m.parents[i]
                if parent.op in bijectiveOps:
                    parentKO = False
                    # This for loop could be omitted if we are sure that parent node has been simplified
                    numChildrenThatAreM = 0
                    for j in range(len(parent.children)):
                        if parent.children[j] is m:
                            numChildrenThatAreM += 1
                        if numChildrenThatAreM == 2:
                            parentKO = True
                            break
                    if not parentKO:
                        assert(numChildrenThatAreM == 1)
                        for child in parent.children:
                            if child is m:
                                continue
                            if leafIsInSubExp(m, child):
                                parentKO = True
                                break

                    #for i2 in range(len(m.parents)):
                    #    if i == i2:
                    #        continue
                    #    parent2 = m.parents[i2]
                    #    if checkNodeInSubExp(parent, parent2):
                    #        parentKO = True
                    #        break

                    if not parentKO:
                        # We compute the depth of parent up the the root of the expression
                        depth = computeDepth(parent)
                        if len(possibleOpNodes[m]) == 0 or depth < possibleOpNodes[m]['depth']:
                            possibleOpNodes[m]['parent'] = parent
                            possibleOpNodes[m]['depth'] = depth


        minDepth = 100000

        # Taking minimum number of occurrences and then minimum depth
        opNode = None
        occList = nbMaskOccurrences.keys()
        occList.sort()
        for nbOcc in occList:
            for mask in nbMaskOccurrences[nbOcc]:
                if len(possibleOpNodes[mask]) != 0 and possibleOpNodes[mask]['depth'] < minDepth:
                    minDepth = possibleOpNodes[mask]['depth']
                    opNode = possibleOpNodes[mask]['parent']
                    maskNode = mask
            # For the first possible opNode, we check all opNodes for the same number of occurrence (considering the smallest depth),
            # But we do not consider masks with a greater number of occurrence once one is found
            if opNode != None:
                break

        if opNode == None:
            # Failure
            # Possible if no 'xor' parent of the masks, for example
            #print('# No mask can be taken')
            if simplifyDone or not simplifyStrategy['FAILURE']:
                return False
            else:
                for n in nodeList:
                    simplify(n, nodeList)
                simplifyDone = True
                continue

        r.add(maskNode)
        assert(maskNode not in nodeList)

        #print('# Replacing %s with %s' % (maskNode.symb, opNode.expPrint()))
        
        # Replacing for example all occurrences of m3 with opNode = 'm3 + (m4 ^ k)'
        # Copying parents so that the created copiedExp cannot be seen as a parent of maskNode...
        parents = list(maskNode.parents)
        checkForMerge = set()
        for parent in parents:
            if parent is opNode:
                continue
            childIdx = 0
            while childIdx < len(parent.children):
                if parent.children[childIdx] is maskNode:
                    maskNode.parents.remove(parent)
                    copiedExp = graph.makeOpNode('^', opNode.children)
                    copiedExp.parents.append(parent)
                    checkForMerge.add(copiedExp)
                    parent.children[childIdx] = copiedExp
                childIdx += 1
        # Performing the substitution of opNode with maskNode
        replaceOpNodeWithMaskNode(opNode, maskNode, nodeList)

        # Merge newly created nodes with their parent if possible
        for node in checkForMerge:
            node.mergeWithParentIfPossible()

        # Simplify
        if alwaysSimplify or simplifyStrategy['REPLACE']:
            for n in nodeList:
                simplify(n, nodeList)
            simplifyDone = True
        else:
            # Reset variable simplifyDone after a replacement except for strategy FAIL_1
            if not simplifyStrategy['SINGLE_REPLACE']:
                simplifyDone = False



