# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from sela import *

def mySimplify(e):
    if True:
        return simp(e)
    else:
        return e

nbExps = 0
nbLeak = 0


firstOrder = True
secondOrder = False

def checkExpLeakageFirstOrder(e0):
    global nbExps
    global nbLeak
    #print('# checkExpLeakage: %s' % e0)
    res, usedBitExp, niTime = checkNIVal(e0)
    nbExps += 1
    if not res:
        nbLeak += 1

    if not res:
        print('# Leakage exp num %d' % (nbExps))


def checkExpLeakageSecondOrder(e0, e1):
    global nbExps
    global nbLeak
    #print('# checkExpLeakage: (%s, %s)' % (e0, e1))
    res, usedBitExp, niTime = checkNITrans(e0, e1)
    nbExps += 1
    if not res:
        nbLeak += 1

    if not res:
        print('# Leakage for exp num %d' % (nbExps))



def gms_and_3s(m0, m1, m2, m3, z12, z13, z23, k0, k1):
    global nbExps
    global nbLeak

    # computing shares
    a1 = m0
    a2 = m1
    a3 = m0 ^ m1 ^ k0

    b1 = m2
    b2 = m3
    b3 = m2 ^ m3 ^ k1;

    signals = []
    signals.append(a1)
    signals.append(a2)
    signals.append(a3)
    signals.append(b1)
    signals.append(b2)
    signals.append(b3)

    # output c = c0 ^ c1 ^ c2 = a & b

    # start analysis
    # Non linear layer
    a1b1 = a1 & b1
    a1b1 = mySimplify(a1b1)
    signals.append(a1b1)

    a1b2 = a1 & b2
    a1b2 = mySimplify(a1b2)
    signals.append(a1b2)

    a1b3 = a1 & b3
    a1b3 = mySimplify(a1b3)
    signals.append(a1b3)

    a2b1 = a2 & b1
    a2b1 = mySimplify(a2b1)
    signals.append(a2b1)

    a2b2 = a2 & b2
    a2b2 = mySimplify(a2b2)
    signals.append(a2b2)

    a2b3 = a2 & b3
    a2b3 = mySimplify(a2b3)
    signals.append(a2b3)

    a3b1 = a3 & b1
    a3b1 = mySimplify(a3b1)
    signals.append(a3b1)

    a3b2 = a3 & b2
    a3b2 = mySimplify(a3b2)
    signals.append(a3b2)

    a3b3 = a3 & b3
    a3b3 = mySimplify(a3b3)
    signals.append(a3b3)

    

    # Linear Layer
    l00 = a1b1 ^ a3b1
    l00 = mySimplify(l00)
    signals.append(l00)
    
    l0 = l00 ^ a1b3
    l0 = mySimplify(l0)
    signals.append(l0)

    l10 = a2b1 ^ a1b2
    l10 = mySimplify(l10)
    signals.append(l10)
    
    l1 = l10 ^ a2b2
    l1 = mySimplify(l1)
    signals.append(l1)

    l20 = a3b2 ^ a2b3
    l20 = mySimplify(l20)
    signals.append(l20)
    
    l2 = l20 ^ a3b3
    l2 = mySimplify(l2)
    signals.append(l2)
     


    # Refreshing Layer
    c10 = l0 ^ z12
    c10 = mySimplify(c10)
    signals.append(c10)
 
    c1 = c10 ^ z13
    c1 = mySimplify(c1)
    signals.append(c1)
 
    c20 = l1 ^ z12
    c20 = mySimplify(c20)
    signals.append(c20)
 
    c2 = c20 ^ z23
    c2 = mySimplify(c2)
    signals.append(c2)
    
    c30 = l2 ^ z13
    c30 = mySimplify(c30)
    signals.append(c30)
 
    c3 = c30 ^ z23
    c3 = mySimplify(c3)
    signals.append(c3)
 
 
    if firstOrder:
        print('# First Order Analysis')
        for s0idx in range(len(signals)):
            checkExpLeakageFirstOrder(signals[s0idx])

        print('# Nb. expressions analysed: %d' % nbExps)
        print('# Nb. expressions leaking: %d' % nbLeak)


    if secondOrder:
        nbExps = 0
        nbLeak = 0
        print('# Second Order Analysis')
        for s0idx in range(len(signals)):
            for s1idx in range(s0idx + 1, len(signals)):
                checkExpLeakageSecondOrder(signals[s0idx], signals[s1idx])

        print('# Nb. expressions analysed: %d' % nbExps)
        print('# Nb. expressions leaking: %d' % nbLeak)


    return c1, c2, c3




if __name__ == '__main__':

    testLitteral = False

    if not testLitteral:
        m0 = symbol('m0', 'M', 1)
        m1 = symbol('m1', 'M', 1)
        m2 = symbol('m2', 'M', 1)
        m3 = symbol('m3', 'M', 1)

        z12 = symbol('z12', 'M', 1)
        z13 = symbol('z13', 'M', 1)
        z23 = symbol('z23', 'M', 1)

        k0 = symbol('k0', 'S', 1)
        k1 = symbol('k1', 'S', 1)
        
        c1, c2, c3 = gms_and_3s(m0, m1, m2, m3, z12, z13, z23, k0, k1)

    else:
        def enumerate_values(t, currIdx):
            if currIdx == len(t):
                m0 = constant(t[0], 1)
                m1 = constant(t[1], 1)
                m2 = constant(t[2], 1)
                m3 = constant(t[3], 1)
                z12 = constant(t[4], 1)
                z13 = constant(t[5], 1)
                z23 = constant(t[6], 1)
                k0 = constant(t[7], 1)
                k1 = constant(t[8], 1)

                c1, c2, c3 = gms_and_3s(m0, m1, m2, m3, z12, z13, z23, k0, k1)
 
                r_ref = k0 & k1
                r_ref = mySimplify(r_ref)
                r = c1 ^ c2 ^ c3
                r = mySimplify(r)

                # Comparing strings ('0' or '1')  because of the two different implementations (either use 'is' or '==')
                if '%s' % r_ref != '%s' % r:
                    print('*** Error for values (%s, %s, %s, %s, %s, %s, %s, %s, %s): result is %s instead of %s' % (m0, m1, m2, m3, z12, z13, z23, k0, k1, r, r_ref))
                    sys.exit(0)
            else:
                t[currIdx] = 0
                enumerate_values(t, currIdx + 1)
                t[currIdx] = 1
                enumerate_values(t, currIdx + 1)

        t = [0] * 9
        enumerate_values(t, 0)
        print('[OK]')


