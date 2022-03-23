#!/usr/bin/python

# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from __future__ import print_function
import timeit

from ni import *
from exp import *
from config import *



def __runCheck(e):
    niTimerStart = timeit.default_timer()
    resNi = ni(e.wordGraph, False)
    if not resNi and bitExpEnable():
        usedBitExp = True
        i = 0
        for b in e.bitGraph.roots:
            #print('# node for bit %d : %s' % (i, b))
            i += 1
        resNi = ni(e.bitGraph, False)
    else:
        usedBitExp = False
    niTimerEnd = timeit.default_timer()
    niTime = niTimerEnd - niTimerStart
    # NI iff 1st arg True, bits Exp used if 2nd arg is true
    return resNi, usedBitExp, niTime


def __runCheckBitExpList(bitExpList):
    totalNiTime = 0
    totalResNi = True

    for bitExp in bitExpList:
        niTimerStart = timeit.default_timer()
        resNi = ni(bitExp.bitGraph, False)
        niTimerEnd = timeit.default_timer()
        niTime = niTimerEnd - niTimerStart
        totalNiTime += niTime
        if not resNi:
            totalResNi = False
            break

    return totalResNi, totalNiTime


def __createExpTransBit(exp0, exp1):
    bitExpList = []
    width = exp0.getWidth()
    for i in range(width):
        bn0 = Extract(i, i, exp0)
        bn1 = Extract(i, i, exp1)
        be = Exp([bn0, bn1])
        bitExpList.append(be)
    return bitExpList


def __createExpTransXorBit(exp0, exp1):
    bitExpList = []
    width = exp0.getWidth()
    for i in range(width):
        bn0 = Extract(i, i, exp0)
        bn1 = Extract(i, i, exp1)
        be = bn0 ^ bn1
        bitExpList.append(be)
    return bitExpList


def checkNIVal_(node):
    e = Exp([node])
    return __runCheck(e)

def checkNITrans_(exp0, exp1):
    e = Exp([exp0, exp1])
    return __runCheck(e)

def checkNITransXor_(exp0, exp1):
    e = exp0 ^ exp1
    res = __runCheck(e)
    return res

def checkNITransBit_(exp0, exp1):
    if bitExpEnable():
        bitExpList = __createExpTransBit(exp0, exp1)
        return __runCheckBitExpList(bitExpList)
    else:
        return False, 0

def checkNITransXorBit_(exp0, exp1):
    if bitExpEnable():
        bitExpList = __createExpTransXorBit(exp0, exp1)
        return __runCheckBitExpList(bitExpList)
    else:
        return False, 0

