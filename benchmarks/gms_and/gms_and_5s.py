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


firstOrder = False
secondOrder = True

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



def gms_and_5s(m0, m1, m2, m3, m4, m5, m6, m7, z12, z13, z14, z15, z23, z24, z25, z34, z35, z45, k0, k1):

    global nbExps
    global nbLeak

    # computing shares
    a1 = m0
    a2 = m1
    a3 = m2
    a4 = m3
    a5 = m0 ^ m1 ^ m2 ^ m3 ^ k0

    b1 = m4
    b2 = m5
    b3 = m6
    b4 = m7
    b5 = m4 ^ m5 ^ m6 ^ m7 ^ k1;

    signals = []
    signals.append(a1)
    signals.append(a2)
    signals.append(a3)
    signals.append(a4)
    signals.append(a5)
    signals.append(b1)
    signals.append(b2)
    signals.append(b3)
    signals.append(b4)
    signals.append(b5)

    # output c = c1 ^ c2 ^ c3 ^ c4 ^ c5 = a & b

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

    a1b4 = a1 & b4
    a1b4 = mySimplify(a1b4)
    signals.append(a1b4)

    a1b5 = a1 & b5
    a1b5 = mySimplify(a1b5)
    signals.append(a1b5)


    a2b1 = a2 & b1
    a2b1 = mySimplify(a2b1)
    signals.append(a2b1)

    a2b2 = a2 & b2
    a2b2 = mySimplify(a2b2)
    signals.append(a2b2)

    a2b3 = a2 & b3
    a2b3 = mySimplify(a2b3)
    signals.append(a2b3)

    a2b4 = a2 & b4
    a2b4 = mySimplify(a2b4)
    signals.append(a2b4)

    a2b5 = a2 & b5
    a2b5 = mySimplify(a2b5)
    signals.append(a2b5)


    a3b1 = a3 & b1
    a3b1 = mySimplify(a3b1)
    signals.append(a3b1)

    a3b2 = a3 & b2
    a3b2 = mySimplify(a3b2)
    signals.append(a3b2)

    a3b3 = a3 & b3
    a3b3 = mySimplify(a3b3)
    signals.append(a3b3)
    
    a3b4 = a3 & b4
    a3b4 = mySimplify(a3b4)
    signals.append(a3b4)

    a3b5 = a3 & b5
    a3b5 = mySimplify(a3b5)
    signals.append(a3b5)


    a4b1 = a4 & b1
    a4b1 = mySimplify(a4b1)
    signals.append(a4b1)

    a4b2 = a4 & b2
    a4b2 = mySimplify(a4b2)
    signals.append(a4b2)

    a4b3 = a4 & b3
    a4b3 = mySimplify(a4b3)
    signals.append(a4b3)
    
    a4b4 = a4 & b4
    a4b4 = mySimplify(a4b4)
    signals.append(a4b4)

    a4b5 = a4 & b5
    a4b5 = mySimplify(a4b5)
    signals.append(a4b5)


    a5b1 = a5 & b1
    a5b1 = mySimplify(a5b1)
    signals.append(a5b1)

    a5b2 = a5 & b2
    a5b2 = mySimplify(a5b2)
    signals.append(a5b2)

    a5b3 = a5 & b3
    a5b3 = mySimplify(a5b3)
    signals.append(a5b3)
    
    a5b4 = a5 & b4
    a5b4 = mySimplify(a5b4)
    signals.append(a5b4)

    a5b5 = a5 & b5
    a5b5 = mySimplify(a5b5)
    signals.append(a5b5)


    # Linear Layer
    l0 = a2b4 ^ a4b2
    l0 = mySimplify(l0)
    signals.append(l0)
    
    l1i = a2b2 ^ a1b2
    l1i = mySimplify(l1i)
    signals.append(l1i)
    
    l1 = l1i ^ a2b1
    l1 = mySimplify(l1)
    signals.append(l1)

    l2 = a4b5 ^ a5b4
    l2 = mySimplify(l2)
    signals.append(l2)
 
    l3i = a1b5 ^ a5b1
    l3i = mySimplify(l3i)
    signals.append(l3i)
    
    l3 = l3i ^ a1b1
    l3 = mySimplify(l3)
    signals.append(l3)

    l4 = a3b5 ^ a5b3
    l4 = mySimplify(l4)
    signals.append(l4)
 
    l5i = a5b5 ^ a2b5
    l5i = mySimplify(l5i)
    signals.append(l5i)
    
    l5 = l5i ^ a5b2
    l5 = mySimplify(l5)
    signals.append(l5)

    l6 = a3b4 ^ a4b3
    l6 = mySimplify(l6)
    signals.append(l6)
 
    l7i = a4b4 ^ a1b4
    l7i = mySimplify(l7i)
    signals.append(l7i)
    
    l7 = l7i ^ a4b1
    l7 = mySimplify(l7)
    signals.append(l7)

    l8 = a2b3 ^ a3b2
    l8 = mySimplify(l8)
    signals.append(l8)
 
    l9i = a3b3 ^ a1b3
    l9i = mySimplify(l9i)
    signals.append(l9i)
    
    l9 = l9i ^ a3b1
    l9 = mySimplify(l9)
    signals.append(l9)


    # Refreshing Layer
    c10i = l0 ^ z45
    c10i = mySimplify(c10i)
    signals.append(c10i)

    c10 = c10i ^ z12
    c10 = mySimplify(c10)
    signals.append(c10)

    c11i = l1 ^ z12
    c11i = mySimplify(c11i)
    signals.append(c11i)

    c11 = c11i ^ z13
    c11 = mySimplify(c11)
    signals.append(c11)

    c20i = l2 ^ z13
    c20i = mySimplify(c20i)
    signals.append(c20i)

    c20 = c20i ^ z14
    c20 = mySimplify(c20)
    signals.append(c20)

    c21i = l3 ^ z14
    c21i = mySimplify(c21i)
    signals.append(c21i)

    c21 = c21i ^ z15
    c21 = mySimplify(c21)
    signals.append(c21)

    c30i = l4 ^ z15
    c30i = mySimplify(c30i)
    signals.append(c30i)

    c30 = c30i ^ z23
    c30 = mySimplify(c30)
    signals.append(c30)

    c31i = l5 ^ z23
    c31i = mySimplify(c31i)
    signals.append(c31i)

    c31 = c31i ^ z24
    c31 = mySimplify(c31)
    signals.append(c31)

    c40i = l6 ^ z24
    c40i = mySimplify(c40i)
    signals.append(c40i)

    c40 = c40i ^ z25
    c40 = mySimplify(c40)
    signals.append(c40)

    c41i = l7 ^ z25
    c41i = mySimplify(c41i)
    signals.append(c41i)

    c41 = c41i ^ z34
    c41 = mySimplify(c41)
    signals.append(c41)

    c50i = l8 ^ z34
    c50i = mySimplify(c50i)
    signals.append(c50i)

    c50 = c50i ^ z35
    c50 = mySimplify(c50)
    signals.append(c50)

    c51i = l9 ^ z35
    c51i = mySimplify(c51i)
    signals.append(c51i)

    c51 = c51i ^ z45
    c51 = mySimplify(c51)
    signals.append(c51)


    # Compression Layer
    c1 = c10 ^ c11
    c1 = mySimplify(c1)
    signals.append(c1)

    c2 = c20 ^ c21
    c2 = mySimplify(c2)
    signals.append(c2)

    c3 = c30 ^ c31
    c3 = mySimplify(c3)
    signals.append(c3)

    c4 = c40 ^ c41
    c4 = mySimplify(c4)
    signals.append(c4)

    c5 = c50 ^ c51
    c5 = mySimplify(c5)
    signals.append(c5)

 
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


    return c1, c2, c3, c4, c5




if __name__ == '__main__':

    testLitteral = False

    if not testLitteral:
        m0 = symbol('m0', 'M', 1)
        m1 = symbol('m1', 'M', 1)
        m2 = symbol('m2', 'M', 1)
        m3 = symbol('m3', 'M', 1)
        m4 = symbol('m4', 'M', 1)
        m5 = symbol('m5', 'M', 1)
        m6 = symbol('m6', 'M', 1)
        m7 = symbol('m7', 'M', 1)

        z12 = symbol('z12', 'M', 1)
        z13 = symbol('z13', 'M', 1)
        z14 = symbol('z14', 'M', 1)
        z15 = symbol('z15', 'M', 1)
        z23 = symbol('z23', 'M', 1)
        z24 = symbol('z24', 'M', 1)
        z25 = symbol('z25', 'M', 1)
        z34 = symbol('z34', 'M', 1)
        z35 = symbol('z35', 'M', 1)
        z45 = symbol('z45', 'M', 1)

        k0 = symbol('k0', 'S', 1)
        k1 = symbol('k1', 'S', 1)

        c1, c2, c3, c4, c5 = gms_and_5s(m0, m1, m2, m3, m4, m5, m6, m7, z12, z13, z14, z15, z23, z24, z25, z34, z35, z45, k0, k1)

    else:
        nb = 0
        def enumerate_values(t, currIdx):
            global nb
            if currIdx == len(t):
                nb += 1
                if nb % 1000 == 0:
                    print('%dk' % (nb / 1000))
                m0 = constant(t[0], 1)
                m1 = constant(t[1], 1)
                m2 = constant(t[2], 1)
                m3 = constant(t[3], 1)
                m4 = constant(t[4], 1)
                m5 = constant(t[5], 1)
                m6 = constant(t[6], 1)
                m7 = constant(t[7], 1)
                z12 = constant(t[8], 1)
                z13 = constant(t[9], 1)
                z14 = constant(t[10], 1)
                z15 = constant(t[11], 1)
                z23 = constant(t[12], 1)
                z24 = constant(t[13], 1)
                z25 = constant(t[14], 1)
                z34 = constant(t[15], 1)
                z35 = constant(t[16], 1)
                z45 = constant(t[17], 1)
                k0 = constant(t[18], 1)
                k1 = constant(t[19], 1)

                c1, c2, c3, c4, c5 = gms_and_5s(m0, m1, m2, m3, m4, m5, m6, m7, z12, z13, z14, z15, z23, z24, z25, z34, z35, z45, k0, k1)
 
                r_ref = k0 & k1
                r_ref = mySimplify(r_ref)
                r = c1 ^ c2 ^ c3 ^ c4 ^ c5
                r = mySimplify(r)

                # Comparing strings ('0' or '1')  because of the two different implementations (either use 'is' or '==')
                if '%s' % r_ref != '%s' % r:
                    print('*** Error for values (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s): result is %s instead of %s' % (m0, m1, m2, m3, m4, m5, m6, m7, z12, z13, z14, z15, z23, z24, z25, z34, z35, z45, k0, k1, r, r_ref))
                    sys.exit(0)
            else:
                t[currIdx] = 0
                enumerate_values(t, currIdx + 1)
                t[currIdx] = 1
                enumerate_values(t, currIdx + 1)

        t = [0] * 20
        enumerate_values(t, 0)
        print('[OK]')


