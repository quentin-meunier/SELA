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



def trichina_and(m0, m1, z, k0, k1):
    global nbExps
    global nbLeak

    # computing shares
    a0 = m0
    a1 = m0 ^ k0

    b0 = m1
    b1 = m1 ^ k1;

    signals = []
    signals.append(a0)
    signals.append(a1)
    signals.append(b0)
    signals.append(b1)


    # output s = s0 ^ s1 = a & b

    # s0 = (a1 & b1 ^ a0 & b1 ^ b0 & a1 ^ a0 & b0) ^ z
    # s1 = z

    c0 = a0 & b0
    c0 = mySimplify(c0)
    signals.append(c0)
    c1 = b0 & a1
    c1 = mySimplify(c1)
    signals.append(c1)
    c2 = a0 & b1
    c2 = mySimplify(c2)
    signals.append(c2)
    c3 = a1 & b1
    c3 = mySimplify(c3)
    signals.append(c3)

    c4 = z ^ c0
    c4 = mySimplify(c4)
    signals.append(c4)
    c5 = c1 ^ c4
    c5 = mySimplify(c5)
    signals.append(c5)
    c6 = c2 ^ c5
    c6 = mySimplify(c6)
    signals.append(c6)
    s0 = c6 ^ c3
    s0 = mySimplify(s0)
    signals.append(s0)

    s1 = z
    s1 = mySimplify(s1)
    signals.append(s1)

    if firstOrder:
        nbExps = 0
        nbLeak = 0
        print('# First Order Analysis')
        for s0idx in range(len(signals)):
            checkExpLeakageFirstOrder(signals[s0idx])

        print('# Nb. expressions analysed: %d' % nbExps)
        print('# Nb. expressions leaking: %d' % nbLeak)

    return s0, s1



if __name__ == '__main__':

    testLitteral = False

    if not testLitteral:
        m0 = symbol('m0', 'M', 1)
        m1 = symbol('m1', 'M', 1)
        z = symbol('z', 'M', 1)

        k0 = symbol('k0', 'S', 1)
        k1 = symbol('k1', 'S', 1)
        
        s0, s1 = trichina_and(m0, m1, z, k0, k1)

    else:
        ok = True
        for m0_v in range(2):
            for m1_v in range(2):
                for z_v in range(2):
                    for k0_v in range(2):
                        for k1_v in range(2):
                            m0 = constant(m0_v, 1)
                            m1 = constant(m1_v, 1)
                            z = constant(z_v, 1)
                            k0 = constant(k0_v, 1)
                            k1 = constant(k1_v, 1)

                            s0, s1 = trichina_and(m0, m1, z, k0, k1)

                            r_ref = k0 & k1
                            r_ref = mySimplify(r_ref)
                            r = s0 ^ s1
                            r = mySimplify(r)
                            
                            # Comparing strings ('0' or '1')  because of the two different implementations (either use 'is' or '==')
                            if '%s' % r_ref != '%s' % r:
                                print('*** Error for values (%s, %s, %s, %s, %s, %s, %s): result is %s instead of %s' % (m0, m1, z, k0, k1, r, r_ref))
                                ok = False
        if ok:
            print('[OK]')



