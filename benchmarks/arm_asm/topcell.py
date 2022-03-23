#!/usr/bin/python

# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from __future__ import print_function
from copy import *

from sela import *
from memory import *


if not useBuiltinExp():
    import z3


class Topcell:

    def __init__(self, instList, startAddress, stopAddress, registerInit, setMemory):
        self.instList = instList
        self.inst = None
        self.memory = Memory('Memory', self, setMemory)

        self.startAddress = startAddress
        self.stopAddress = stopAddress
        self.analysing = False
        self.debug = False
        self.trace = False

        self.regfile = [None] * 16
        for i in range(16):
            self.regfile[i] = registerInit[i]

        self.regfileNew = [None] * 16

        # Analysis results
        self.nbAnalysedInsts = 0
        self.nbAnalysis = {}
        self.nbNIInstsLeakageVal = {}
        self.nonNIInstsLeakageVal = {}
        self.nbNIInstsLeakageTransBit = {}
        self.nonNIInstsLeakageTransBit = {}
        self.nbNIInstsLeakageTrans = {}
        self.nonNIInstsLeakageTrans = {}
        self.nbNIInstsLeakageTransXorBit = {}
        self.nonNIInstsLeakageTransXorBit = {}
        self.nbNIInstsLeakageTransXor = {}
        self.nonNIInstsLeakageTransXor = {}
        for i in range(16):
            self.nbAnalysis[i] = 0
            self.nbNIInstsLeakageVal[i] = 0
            self.nonNIInstsLeakageVal[i] = []
            self.nbNIInstsLeakageTransBit[i] = 0
            self.nonNIInstsLeakageTransBit[i] = []
            self.nbNIInstsLeakageTrans[i] = 0
            self.nonNIInstsLeakageTrans[i] = []
            self.nbNIInstsLeakageTransXorBit[i] = 0
            self.nonNIInstsLeakageTransXorBit[i] = []
            self.nbNIInstsLeakageTransXor[i] = 0
            self.nonNIInstsLeakageTransXor[i] = []


    def advanceCycle(self):
        if self.trace:
            print('# Advance Cycle')
        if len(self.instList) != 0:
            self.inst = self.instList.pop(0)
        else:
            return True

        if not self.analysing and self.inst.addr == self.startAddress:
            if self.trace:
                print('### Start analysis ###')
            self.analysing = True
        elif self.analysing and self.inst.addr == self.stopAddress:
            self.analysing = False

        # Instruction does not write PC register
        pcVal = self.inst.addr - 1
        if pcVal % 4 == 0:
            pcVal += 4
        else:
            pcVal += 2
        assert(pcVal % 4 == 0)
        self.regfile[15] = constant(pcVal, 32)

        if self.trace:
            print('# Executing instruction %s' % self.inst)


    def analyse(self):
        if self.trace:
            print('# Analysis')
        if self.analysing:
            self.nbAnalysedInsts += 1
            for i in range(16):
                if self.regfileNew[i] != None:
                    self.nbAnalysis[i] += 1

                    v0 = self.regfile[i]
                    v1 = self.regfileNew[i]

                    res, wordRes, niTime = checkNIVal(v1)
                    if res:
                        self.nbNIInstsLeakageVal[i] += 1
                    else:
                        if self.trace:
                            print('# Leakage in value for r%d and exp %s' % (i, v1))
                        self.nonNIInstsLeakageVal[i].append(self.inst.addr)

                    res, wordRes, niTime = checkNITrans(v0, v1)
                    if res:
                        self.nbNIInstsLeakageTrans[i] += 1
                    else:
                        print('# Leakage in transition for         r%d and exps [%s, %s]' % (i, v0, v1))
                        self.nonNIInstsLeakageTrans[i].append(self.inst.addr)

                    res, niTime = checkNITransBit(v0, v1)
                    if res:
                        self.nbNIInstsLeakageTransBit[i] += 1
                    else:
                        print('# Leakage in transition bit for     r%d and exps [%s, %s]' % (i, v0, v1))
                        self.nonNIInstsLeakageTransBit[i].append(self.inst.addr)

                    res, wordRes, niTime = checkNITransXor(v0, v1)
                    if res:
                        self.nbNIInstsLeakageTransXor[i] += 1
                    else:
                        print('# Leakage in transition xor for     r%d and exps [%s, %s]' % (i, v0, v1))
                        self.nonNIInstsLeakageTransXor[i].append(self.inst.addr)

                    res, niTime = checkNITransXorBit(v0, v1)
                    if res:
                        self.nbNIInstsLeakageTransXorBit[i] += 1
                    else:
                        print('# Leakage in transition xor bit for r%d and exps [%s, %s]' % (i, v0, v1))
                        self.nonNIInstsLeakageTransXorBit[i].append(self.inst.addr)


        # Reset regfileNew
        for i in range(16):
            if self.regfileNew[i] != None:
                self.regfile[i] = self.regfileNew[i]
                self.regfileNew[i] = None



    def computeOutput(self):
        if self.trace:
            print('# Compute output')
        inst = self.inst
        if inst == None:
            return

        op = inst.op
        ra = inst.ra
        rb = inst.rb
        rc = inst.rc
        rd = inst.rd
        imm = inst.imm
        sh = inst.sh
        shOp = inst.shOp
        wbPre = inst.wbPre
        wbPost = inst.wbPost
        regfile = self.regfile
        regfileNew = self.regfileNew
        memory  = self.memory

        if wbPre or wbPost:
            if inst.isLoad():
                regWB = ra
                regIncWB = rb
            else:
                assert(inst.isStore())
                regWB = rb
                regIncWB = rc # can be None (if str immediate)
            if inst.isLoadRegOffset() or inst.isStoreRegOffset():
                assert(imm == None or imm == 0)
                if shOp == None:
                    assert(sh == None)
                    regfileNew[regWB] = regfile[regWB] + regfile[regIncWB]
                elif shOp == 'lsl':
                    regfileNew[regWB] = regfile[regWB] + (regfile[regIncWB] << sh)
                elif shOp == 'lsr':
                    regfileNew[regWB] = regfile[regWB] + LShR(regfile[regIncWB], sh)
                elif shOp == 'asr':
                    regfileNew[regWB] = regfile[regWB] + (regfile[regIncWB] >> sh)
                elif shOp == 'ror':
                    # Not implemented
                    assert(False)
            else:
                assert(sh == None)
                regfileNew[regWB] = regfile[regWB] + constant(imm, 32)

            regfileNew[regWB] = simp(regfileNew[regWB])

            if self.debug:
                print('# r%d <- 0x%x [WB %s]' % (regWB, int(str(regfileNew[regWB])), wbPre and 'Pre' or 'Post'))

        if inst.isLoad():
            baseAddr = regfile[ra]
            if wbPost:
                # For WB Post instructions, access is always made at address [ra]
                offset = 0
            else:
                if inst.isLoadRegOffset():
                    assert(imm == None or imm == 0)
                    if shOp == None:
                        assert(sh == None)
                        offset = regfile[rb]
                    elif shOp == 'lsl':
                        offset = regfile[rb] << sh
                    elif shOp == 'lsr':
                        offset = LShR(regfile[rb], sh)
                    elif shOp == 'asr':
                        offset = regfile[rb] >> sh
                    elif shOp == 'ror':
                        # Not implemented
                        assert(False)
                else:
                    assert(sh == None)
                    offset = constant(imm, 32)

            if inst.size == 4:
                regfileNew[rd] = memory.ldr(baseAddr, offset)
            else:
                assert(inst.size == 1)
                regfileNew[rd] = ZeroExt(24, memory.ldrb(baseAddr, offset))

            regfileNew[rd] = simp(regfileNew[rd])

            if self.debug:
                try:
                    valHexa = ' [0x%x]' % int(str(regfileNew[rd]))
                except:
                    valHexa = ''
                print('# r%d <- %s%s' % (rd, regfileNew[rd], valHexa))

        elif inst.isStore():
            baseAddr = regfile[rb]
            if wbPost:
                # For WB Post instructions, access is always made at address [rb]
                offset = 0
            else:
                if inst.isStoreRegOffset():
                    assert(imm == None or imm == 0)
                    if shOp == None:
                        assert(sh == None)
                        offset = regfile[rc]
                    elif shOp == 'lsl':
                        offset = regfile[rc] << sh
                    elif shOp == 'lsr':
                        offset = LShR(regfile[rc], sh)
                    elif shOp == 'asr':
                        offset = regfile[rc] >> sh
                    elif shOp == 'ror':
                        # Not implemented
                        assert(False)
                else:
                    assert(sh == None)
                    offset = constant(imm, 32)

            if inst.size == 4:
                memory.strw(baseAddr, offset, regfile[ra])
            else:
                assert(inst.size == 1)
                memory.strb(baseAddr, offset, regfile[ra])

        elif op in Instruction.writesRegBank():
            if ra == None:
                assert(shOp == None)
                valA = constant(imm, 32)
            else:
                valA = regfile[ra]

            if shOp == None:
                if rb != None:
                    valB = regfile[rb]
                    assert(sh == None)
                else:
                    valB = constant(imm, 32)
            elif shOp == 'lsl':
                assert(imm == None or imm == 0)
                if sh == None:
                    valB = regfile[rb] << regfile[rc]
                else:
                    valB = regfile[rb] << sh
            elif shOp == 'lsr':
                assert(imm == None or imm == 0)
                if sh == None:
                    valB = LShR(regfile[rb], regfile[rc])
                else:
                    valB = LShR(regfile[rb], sh)
            elif shOp == 'asr':
                assert(imm == None or imm == 0)
                if sh == None:
                    valB = regfile[rb] >> regfile[rc]
                else:
                    valB = regfile[rb] >> sh
            elif shOp == 'ror':
                assert(imm == None or imm == 0)
                if sh == None:
                    valB = RotateRight(regfile[rb], regfile[rc])
                else:
                    valB = RotateRight(regfile[rb], sh)

            if op == 'eor' or op == 'eors' or op == 'eor.w':
                regfileNew[rd] = valA ^ valB
            elif op == 'ors':
                regfileNew[rd] = valA | valB
            elif op == 'and':
                regfileNew[rd] = valA & valB
            elif op == 'add' or op == 'adds':
                regfileNew[rd] = valA + valB
            elif op == 'sub' or op == 'subs' or op == 'subs.w':
                regfileNew[rd] = valA - valB
            elif op == 'mov' or op == 'mov.w' or op == 'movs':
                regfileNew[rd] = valA
            elif op == 'not':
                regfileNew[rd] = ~valA
            elif op == 'sbfx':
                regfileNew[rd] = SignExt(32 - inst.width, Extract(imm + inst.width - 1, imm, valA))
            elif op == 'ubfx':
                regfileNew[rd] = ZeroExt(32 - inst.width, Extract(imm + inst.width - 1, imm, valA))
            elif op == 'uxtb':
                regfileNew[rd] = ZeroExt(24, Extract(7, 0, valA))
            elif op == 'lsl' or op == 'lsls':
                if imm == None:
                    regfileNew[rd] = regfile[ra] << regfile[rb]
                else:
                    regfileNew[rd] = regfile[ra] << imm
            elif op == 'lsr' or op == 'lsrs':
                if imm == None:
                    regfileNew[rd] = LShR(regfile[ra], regfile[rb])
                else:
                    regfileNew[rd] = LShR(regfile[ra], imm)
            elif op == 'asr' or op == 'asrs':
                if imm == None:
                    regfileNew[rd] = regfile[ra] >> regfile[rb]
                else:
                    regfileNew[rd] = regfile[ra] >> imm
            elif op == 'ror':
                if imm == None:
                    regfileNew[rd] = RotateRight(regfile[ra], regfile[rb])
                else:
                    regfileNew[rd] = RotateRight(regfile[ra], imm)
            else:
                assert(False)

            regfileNew[rd] = simp(regfileNew[rd])
            if self.debug:
                try:
                    valHexa = ' [0x%x]' % int(str(regfileNew[rd]))
                except:
                    valHexa = ''
                print('# r%d <- %s%s' % (rd, regfileNew[rd], valHexa))


    def displayResultsSingleLeakageModel(self, nbNIInsts, nonNIInsts):
        nbExpsAnalysed = sum(self.nbAnalysis.values())
        nbTotalLeakages = nbExpsAnalysed - sum(getattr(self, nbNIInsts).values())
        print('# %d leakages found / %d expressions analysed' % (nbTotalLeakages, nbExpsAnalysed))
        for i in range(16):
            if self.nbAnalysis[i] == 0:
                print('# reg %2d: -' % (i))
                continue
            print('# reg %2d: %3d / %3d leakage-free instruction' % (i, getattr(self, nbNIInsts)[i], self.nbAnalysis[i]))
            nonNI = getattr(self, nonNIInsts)[i]
            if len(nonNI) != 0:
                print('#    Non leakage-free instructions:')
                nonNI.sort()
                m = {}
                for addr in nonNI:
                    if addr in m:
                        m[addr] += 1
                    else:
                        m[addr] = 1
                l = m.keys()
                l.sort()
                for addr in l:
                    print('#    [0x%x] : %d' % (int(str(addr)), m[addr]))


    def displayResults(self):
        print('###########################')
        print('###       Results       ###')
        print('###########################')
        testLitteral = False
        if testLitteral:
            print('### c0: 0x%x' % int(str(simp(self.memory.mem[0x18a10]))))
            print('### c1: 0x%x' % int(str(simp(self.memory.mem[0x18a0d]))))
            return
        print('### %d instructions in analysed region' % self.nbAnalysedInsts)
        print('### Results for leakage in value ###')
        self.displayResultsSingleLeakageModel('nbNIInstsLeakageVal', 'nonNIInstsLeakageVal')
        print('### Results for leakage in transition ###')
        self.displayResultsSingleLeakageModel('nbNIInstsLeakageTrans', 'nonNIInstsLeakageTrans')
        print('### Results for leakage in transition per bit ###')
        self.displayResultsSingleLeakageModel('nbNIInstsLeakageTransBit', 'nonNIInstsLeakageTransBit')
        print('### Results for leakage in transition xor ###')
        self.displayResultsSingleLeakageModel('nbNIInstsLeakageTransXor', 'nonNIInstsLeakageTransXor')
        print('### Results for leakage in transition xor per bit ###')
        self.displayResultsSingleLeakageModel('nbNIInstsLeakageTransXorBit', 'nonNIInstsLeakageTransXorBit')





