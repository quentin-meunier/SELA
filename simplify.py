#!/usr/bin/python

# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from __future__ import print_function

from node import *
from graph import *


# FIXME: verifier les deregister: n not in nodeList (sinon ne pas deregister)
#        si duplication systematique, ne devrait plus etre le cas?
#        (copie de reference faite au moins dans SignExt, et peut-etre dans add/sub)
# A terme, pour les noeuds 'node' qui ne sont pas des feuilles :
#        * Il doit y avoir equivalence entre : len(node.parents) == 0 <=> node in g.roots
#        * node in g.roots => count(g.roots, node) = 1 (ref. unique)
def simplify(node, nodeList):
    if not node.children:
        return
    #print('# Simplifying node %s' % node.expPrint())
    assert(isinstance(node, OpNode))
    #for child in node.children:
    #    simplify(child, nodeList)
    for idx in range(len(node.children)):
        simplify(node.children[idx], nodeList)
    
    #print('# Merging children of node %s' % node.expPrint())
    # Trying to merge current node with its children if associative and children have the same op
    node.mergeWithChildrenIfPossible()
    #print('# Continuing simplify with node %s' % node.expPrint())

    # ZeroExt(n, k) ^ ZeroExt(n, m) -> ZeroExt(n, k ^ m)
    if isinstance(node, OpNode) and (node.op == '^' or node.op == '&' or node.op == '|'):
        allChildrenZeroExt = True
        allChildrenSignExt = True
        for child in node.children:
            if not isinstance(child, OpNode):
                allChildrenZeroExt = False
                allChildrenSignExt = False
                break
            if child.op != 'ZE' or child.children[0].cst != node.children[0].children[0].cst:
                allChildrenZeroExt = False
                if not allChildrenSignExt:
                    break
            if child.op != 'SE' or child.children[0].cst != node.children[0].children[0].cst:
                allChildrenSignExt = False
                if not allChildrenZeroExt:
                    break
        if allChildrenZeroExt or allChildrenSignExt:
            extType = node.children[0].op
            extWidthNode = node.children[0].children[0]
            # Suppressing all Ext nodes in children
            for child in node.children:
                Node.unlink(child.children[0], child)
                Node.linkChildAndParent(child, nodeList)
            # Update node.width
            node.width = node.children[0].width
            # Inserting ExtNode above current node
            # It is required that at the end of this transform, the current node is the ^ (or &, |) node
            # so that it is simplified regularly in the following
            if len(node.parents) == 0:
                # Creating newExtNode here, because if created before, it will
                # copy all the subgraph if node already has parents
                newExtNode = node.graph.makeOpNode(extType, [extWidthNode, node])
                assert(node in nodeList)
                for i in range(len(nodeList)):
                    if nodeList[i] is node:
                        nodeList[i] = newExtNode
            else:
                parent = node.parents[0]
                assert(parent.children.count(node) == 1)
                # Saving index
                for i in range(len(parent.children)):
                    if parent.children[i] is node:
                        idx = i
                        break
                # Unlinking node from its parent before creating newExtNode
                # Unlinking node without calling unlink to keep the index of node in node.parents for the future node (newExtNode)
                parent.children[idx] = None
                node.parents.remove(parent)

                newExtNode = node.graph.makeOpNode(extType, [extWidthNode, node])
                parent.children[idx] = newExtNode
                newExtNode.parents.append(parent)

    nbBits = node.width
    if isinstance(node, OpNode) and node.op == '^':
        # simplify e ^ 0 to e
        # simplify e ^ e to 0
        # simplify e ^ 1 to ~e
        # simplify ~a ^ ~b ^ ~c to ~(a ^ b ^ c)
        i = 0
        addNotNode = False
        # Necessary to cut into two while loops: the exp k0 ^ ~k0 will not be simplfied in one pass
        # (the ~ would be removed when processing the second child and then the comparison with the first child would not be done)
        while i < len(node.children):
            child0 = node.children[i]
            if isinstance(child0, ConstNode) and child0.cst == 0:
                Node.unlink(child0, node, i)
                continue
            if isinstance(child0, ConstNode) and child0.cst == (1 << nbBits) - 1:
                addNotNode = not addNotNode
                Node.unlink(child0, node, i)
                continue
            if isinstance(child0, OpNode) and child0.op == '~':
                addNotNode = not addNotNode
                # Removing not node
                Node.linkChildAndParent(child0, nodeList)
            i += 1
        # Calling mergeWithChildrenIfPossible
        # because removing '~' node can make '^' nodes as children
        # (Note those '^' nodes should not have any '~' children)
        node.mergeWithChildrenIfPossible()

        i = 0
        while i < len(node.children):
            child0 = node.children[i]
            j = i + 1
            removed = False
            while j < len(node.children):
                child1 = node.children[j]
                if equivalence(child0, child1):
                    # Suppressing child0 and child1
                    Node.unlink(child0, node, i)
                    child0.removeSymbRefs(nodeList)

                    # since i < j, index of child1 is j - 1
                    Node.unlink(child1, node, j - 1)
                    child1.removeSymbRefs(nodeList)

                    removed = True
                    break
                j += 1
            if not removed:
                i += 1

        if len(node.children) == 1 or len(node.children) == 0:
            # We suppress the xor node
            if len(node.children) == 1:
                if addNotNode:
                    child = node.children[0]
                    if isinstance(child, OpNode) and child.op == '~':
                        # Suppress existing not node instead of adding one
                        Node.linkChildAndParent(child, nodeList)
                    else:
                        # Replacing xor with not, and do not suppress node
                        node.op = '~'
                        return
            else:
                if addNotNode:
                    child = node.graph.makeConstNode((1 << nbBits) - 1, nbBits)
                else:
                    child = node.graph.makeConstNode(0, nbBits)
                Node.link(child, node)

            # Suppressing xor node
            Node.linkChildAndParent(node, nodeList)
        elif addNotNode:
            if len(node.parents) == 0:
                assert(node in nodeList)
                notNode = node.graph.makeOpNode('~', [node])
                # Replacing (the possibly multiple occurrences of) node in nodeList by newly created notNode
                for idx in range(len(nodeList)):
                    if nodeList[idx] is node:
                        nodeList[idx] = notNode
            else:
                assert(len(node.parents) == 1)
                # Insert 'not' between node and node.parents[0]
                # Note: the index must be the same! (calling simplfy on children in order)
                # Note: first child being node is correct since, as it is an OpNode, it can have only one parent
                parentNode = node.parents[0]
                for idx in range(len(parentNode.children)):
                    if parentNode.children[idx] is node:
                        # Cutting node before creating a new parent to avoid deep copy
                        #Node.unlink(node, parentNode, idx)
                        #notNode = node.graph.makeOpNode('~', [node])
                        #Node.link(notNode, parentNode, idx)
                        ## or
                        node.parents.remove(parentNode)
                        notNode = node.graph.makeOpNode('~', [node])
                        parentNode.children[idx] = notNode
                        notNode.parents.append(parentNode)
                        break


    elif isinstance(node, OpNode) and node.op == '+':
        i = 0
        lastChildConstNode = None
        # First pass: constants
        while i < len(node.children):
            child = node.children[i]
            if isinstance(child, ConstNode) and child.cst == 0 and len(node.children) > 1:
                # Removing child if it is constant 0 and not the last child
                Node.unlink(child, node, i)
                continue

            elif isinstance(child, ConstNode):
                if lastChildConstNode == None:
                    lastChildConstNode = child
                else:
                    # Adding two constants in a new node and unlinking both nodes
                    # (unlinking first occurrence for lastChildConstNode is OK)
                    # Replacing child with newConstNode and linking/unlinking parent part here
                    newConstNode = node.graph.makeConstNode((lastChildConstNode.cst + child.cst) % (1 << nbBits), nbBits)
                    node.children[i] = newConstNode
                    child.parents.remove(node)
                    newConstNode.parents.append(node)

                    Node.unlink(lastChildConstNode, node)
                    lastChildConstNode = newConstNode
                    continue
            i += 1

        # 2nd pass: equivalence: removing opposite expressions
        i = 0
        while i < len(node.children):
            child0 = node.children[i]
            j = i + 1
            removed = False
            while j < len(node.children):
                child1 = node.children[j]
                
                if isinstance(child0, OpNode) and child0.op == '-' and equivalence(child0.children[0], child1) or isinstance(child1, OpNode) and child1.op == '-' and equivalence(child0, child1.children[0]):
                    # Suppressing child0 and child1
                    Node.unlink(child0, node, i)
                    child0.removeSymbRefs(nodeList)

                    # since i < j, index of child1 is j - 1
                    Node.unlink(child1, node, j - 1)
                    child1.removeSymbRefs(nodeList)

                    removed = True
                    break
                j += 1
            if not removed:
                i += 1

        if len(node.children) == 1:
            # Suppressing '+' node
            Node.linkChildAndParent(node, nodeList)
        elif len(node.children) == 0:
            child = node.graph.makeConstNode(0, nbBits)
            Node.link(child, node)
            Node.linkChildAndParent(node, nodeList)
     

    elif isinstance(node, OpNode) and node.op == '-':
        assert(len(node.children) == 1)
        assert(not isinstance(node.children[0], ConstNode))
        # -(-e) -> e
        child = node.children[0]
        if isinstance(child, OpNode) and child.op == '-':
            Node.linkChildAndParent(child, nodeList)
            Node.linkChildAndParent(node, nodeList)


    elif isinstance(node, OpNode) and (node.op == '&' or node.op == '|'):
        # simplify e & 0 to 0, e & 1 to e
        # simplify e | 0 to e, e | 1 to 1
        # simplify e & e and e | e to e
        i = 0
        while i < len(node.children):
            child0 = node.children[i]

            if node.op == '&' and isinstance(child0, ConstNode) and child0.cst == 0:
                idx = 0
                while len(node.children) != 1:
                    # Removing all children except constant 0 (node child0)
                    child = node.children[idx]
                    if idx == 0 and child is child0:
                        idx = 1
                        continue
                    Node.unlink(child, node, idx)
                    child.removeSymbRefs(nodeList)
                break
            elif node.op == '|' and isinstance(child0, ConstNode) and child0.cst == (1 << nbBits) - 1:
                idx = 0
                while len(node.children) != 1:
                    # Removing all children except constant 1
                    child = node.children[idx]
                    if idx == 0 and child is child0:
                        idx = 1
                        continue
                    Node.unlink(child, node, idx)
                    child.removeSymbRefs(nodeList)
                break
            elif (node.op == '&' and isinstance(child0, ConstNode) and child0.cst == (1 << nbBits) - 1) or (node.op == '|' and isinstance(child0, ConstNode) and child0.cst == 0):
                # Removing node child0, except if last node
                if len(node.children) > 1:
                    Node.unlink(child0, node, i)
                    #child0.removeSymbRefs(nodeList)
                    continue
                else:
                    break
            j = i + 1
            while j < len(node.children):
                child1 = node.children[j]
                if equivalence(child0, child1):
                    # Suppressing child1
                    Node.unlink(child1, node, j)
                    child1.removeSymbRefs(nodeList)
                else:
                    j += 1
            i += 1

        assert(len(node.children) > 0)
        if len(node.children) == 1:
            # Suppressing '&' or '|' node
            Node.linkChildAndParent(node, nodeList)

    elif isinstance(node, OpNode) and node.op == '~':
        assert(len(node.children) == 1)
        child = node.children[0]
        if isinstance(child, OpNode) and child.op == '~':
            Node.linkChildAndParent(child, nodeList)
            Node.linkChildAndParent(node, nodeList)
        elif isinstance(child, ConstNode) and child.cst == 0:
            Node.unlink(child, node)
            newConstNode = node.graph.makeConstNode((1 << nbBits) - 1, nbBits)
            Node.link(newConstNode, node)
            # Suppressing not node
            Node.linkChildAndParent(node, nodeList)
        elif isinstance(child, ConstNode) and child.cst == (1 << nbBits) - 1:
            Node.unlink(child, node)
            newConstNode = node.graph.makeConstNode(0, nbBits)
            Node.link(newConstNode, node)
            # Suppressing not node
            Node.linkChildAndParent(node, nodeList)

    elif isinstance(node, OpNode) and (node.op == 'E'):
        simplifyExtract(node, nodeList)
    elif isinstance(node, OpNode) and (node.op == 'C'):
        # Case all children constants
        allChildrenCst = True
        for child in node.children:
            if not isinstance(child, ConstNode):
                allChildrenCst = False
                break
        if allChildrenCst:
            cstRes = 0
            currNbBits = 0
            for child in node.children:
                cstRes += child.cst << currNbBits
                currNbBits += child.width
            newConstNode = node.graph.makeConstNode(cstRes, currNbBits)
            # Suppressing current children
            while len(node.children) > 0:
                Node.unlink(node.children[0], node)
            Node.link(newConstNode, node)
            # Suppressing Extract node
            Node.linkChildAndParent(node, nodeList)
            return

        currentBit = 0
        # Case children are Extract nodes with correct bit indexes first
        for child in node.children:
            if isinstance(child, OpNode) and child.op == 'E' and child.children[1].cst == currentBit:
                currentBit = child.children[0].cst + 1
            else:
                return
        # Checking if all children are equivalent expressions
        for childNum in range(1, len(node.children)):
            if not equivalence(node.children[0].children[2], node.children[childNum].children[2]):
                return

        # FIXME: what if currentBit != node.width? an Extract should be kept
        # Also, current bit should not necessarily start at 0...

        # Suppressing Extract Nodes and keeping only first child
        while len(node.children) > 1:
            child = node.children[1]
            Node.unlink(child, node)
            child.removeSymbRefs(nodeList)
        extractNode = node.children[0]
        child = extractNode.children[2]
        msbNode = extractNode.children[0]
        lsbNode = extractNode.children[1]
        Node.unlink(msbNode, extractNode)
        Node.unlink(lsbNode, extractNode)
        # Suppressing Extract Node
        Node.linkChildAndParent(extractNode, nodeList)
        # Suppressing Concat Node
        Node.linkChildAndParent(node, nodeList)

    elif isinstance(node, OpNode) and (node.op == 'ZE'):
        if isinstance(node.children[1], ConstNode):
            numZeros = node.children[0]
            child = node.children[1]
            cst = child.cst
            childNbBits = child.width
            if cst < 0:
                cst = cst % (1 << childNbBits)
            assert(nbBits == childNbBits + numZeros.cst)
            newConstNode = node.graph.makeConstNode(cst, nbBits)
            while len(node.children) > 0:
                Node.unlink(node.children[0], node)
            Node.link(newConstNode, node)
            # Suppressing ZeroExt node
            Node.linkChildAndParent(node, nodeList)


def simplifyExtract(node, nodeList):
    # No recursion
    child = node.children[2]
    msbNode = node.children[0]
    msb = msbNode.cst
    lsbNode = node.children[1]
    lsb = lsbNode.cst
    if isinstance(child, ConstNode):
        # Extract bitfield from constant
        cst = child.cst
        childWidth = child.width
        cstString = format(cst, '0%db' % childWidth)[::-1]
        newCstString = cstString[lsb:msb + 1]
        newCst = int(newCstString[::-1], 2)
        newConstNode = node.graph.makeConstNode(newCst, msb - lsb + 1)
        # Replacing current children with newConstNode
        # All 3 children are ConstNodes, no need to removeSymbRefs
        Node.unlink(child, node)
        Node.unlink(msbNode, node)
        Node.unlink(lsbNode, node)
        Node.link(newConstNode, node)
        # Suppressing Extract node
        Node.linkChildAndParent(node, nodeList)
    elif isinstance(child, OpNode) and (child.op == 'SE' or child.op == 'ZE'):
        # +----------------+------+
        # |     ZExt       |  e   |
        # +----------------+------+
        #         \--- Extract ---/
        extendNode = child
        extendValue = extendNode.children[0].cst
        child = extendNode.children[1]
        if child.width - 1 >= msb:
            # Remove SE or ZE node: first remove constant node
            Node.unlink(extendNode.children[0], extendNode)
            Node.linkChildAndParent(extendNode, nodeList)
            if lsb == 0 and msb == child.width - 1:
                # Also remove ExtractNode
                Node.unlink(msbNode, node)
                Node.unlink(lsbNode, node)
                Node.linkChildAndParent(node, nodeList)
        elif lsb == 0:
            # We also have msb > child.width - 1
            # We can remove the Extract node if we modify the Extension length
            extendWidth = node.width - child.width
            extendNode.children[0] = node.graph.makeConstNode(extendWidth, extendWidth.bit_length())
            extendNode.width = node.width
            Node.unlink(msbNode, node)
            Node.unlink(lsbNode, node)
            Node.linkChildAndParent(node, nodeList)
    elif isinstance(child, OpNode) and child.op == 'C':
        concatNode = child
        startBitIdx = lsb
        removedBitsOnRight = 0
        while concatNode.children[0].width <= startBitIdx:
            concatChild = concatNode.children[0]
            concatChildWidth = concatChild.width
            startBitIdx -= concatChildWidth
            removedBitsOnRight += concatChildWidth
            # remove child 0
            Node.unlink(concatChild, concatNode)
            concatChild.removeSymbRefs(nodeList)
        concatNode.width -= removedBitsOnRight
        endBitIdx = msb - removedBitsOnRight
        lsbNode.cst -= removedBitsOnRight
        msbNode.cst -= removedBitsOnRight
        leftChildIdx = 0
        currBitIdx = concatNode.children[leftChildIdx].width - 1
        while currBitIdx < endBitIdx:
            leftChildIdx += 1
            currBitIdx += concatNode.children[leftChildIdx].width
        # Removing children on the left of the Concat node
        leftChildIdx += 1
        while len(concatNode.children) > leftChildIdx:
            # remove child
            concatChild = concatNode.children[leftChildIdx]
            concatNode.width -= concatChild.width
            Node.unlink(concatChild, concatNode)
            concatChild.removeSymbRefs(nodeList)
        if len(concatNode.children) == 1:
            # Remove Concat node
            Node.linkChildAndParent(concatNode, nodeList)
        if lsbNode.cst == 0 and msbNode.cst == currBitIdx:
            # Remove Extract node if start and end bits are aligned
            Node.unlink(lsbNode, node)
            Node.unlink(msbNode, node)
            node.linkChildAndParent(node, nodeList)




def equivalence(node0, node1):
    #FIXME: check that node0.width == node1.width ?
    # and return False?
    if isinstance(node0, SymbNode) and isinstance(node1, SymbNode):
        return node0.symb == node1.symb
    elif isinstance(node0, ConstNode) and isinstance(node1, ConstNode):
        return node0.cst == node1.cst
    elif isinstance(node0, OpNode) and isinstance(node1, OpNode) and node0.op == node1.op and len(node0.children) == len(node1.children):
        assert(len(node0.children) > 0)
        if node0.op in associativeOps:
            idx0 = 0
            equivChildren1 = {node:node1.children.count(node) for node in node1.children}
            while idx0 < len(node0.children):
                # Trying to find child in node1 equivalent to node0.children[idx0]
                child0 = node0.children[idx0]
                child0Treated = False
                for child1 in node1.children:
                    if equivChildren1[child1] == 0:
                        continue
                    if equivalence(child0, child1):
                        idx0 += 1
                        equivChildren1[child1] -= 1
                        child0Treated = True
                        break
                if not child0Treated:
                    return False
            return True
        else:
            # not associative op
            for i in range(len(node0.children)):
                if not equivalence(node0.children[i], node1.children[i]):
                    return False
            return True




