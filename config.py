#!/usr/bin/python

# Copyright (C) 2019, Sorbonne Universite, LIP6
# This file is part of the SELA project, under the GPL v3.0 license
# See https://www.gnu.org/licenses/gpl-3.0.en.html for license information
# SPDX-License-Identifier: GPL-3.0-only
# Author(s): Quentin L. Meunier

from __future__ import print_function

simplifyStrategy = {'FULL_RETRY': False,
                    'START': True,
                    'FAILURE': False,
                    'REPLACE': True,
                    'SINGLE_REPLACE': False}

strategies = ['START_REPLACE', 'START', 'REPLACE', 'NONE', 'FAIL', 'START_FAIL', 'FAIL_REPLACE', 'FAIL_1']
propagateCst = True
mergeAssociativeOps = True
simplifyBuild = True
bitExp = True
builtinExp = True

def setSimplifyStrategy(tag):
    global simplifyStrategy
    simplifyStrategy['SINGLE_REPLACE'] = False
    if tag == 'START_REPLACE':
        simplifyStrategy['FULL_RETRY'] = False
        simplifyStrategy['START'] = True
        simplifyStrategy['FAILURE'] = False
        simplifyStrategy['REPLACE'] = True
    elif tag == 'START':
        simplifyStrategy['START'] = True
        simplifyStrategy['FAILURE'] = False
        simplifyStrategy['REPLACE'] = False
    elif tag == 'REPLACE':
        simplifyStrategy['START'] = False
        simplifyStrategy['FAILURE'] = False
        simplifyStrategy['REPLACE'] = True
    elif tag == 'NONE':
        simplifyStrategy['START'] = False
        simplifyStrategy['FAILURE'] = False
        simplifyStrategy['REPLACE'] = False
    elif tag == 'FAIL':
        simplifyStrategy['START'] = False
        simplifyStrategy['FAILURE'] = True
        simplifyStrategy['REPLACE'] = False
    elif tag == 'START_FAIL':
        simplifyStrategy['START'] = True
        simplifyStrategy['FAILURE'] = True
        simplifyStrategy['REPLACE'] = False
    elif tag == 'FAIL_REPLACE':
        simplifyStrategy['START'] = False
        simplifyStrategy['FAILURE'] = True
        simplifyStrategy['REPLACE'] = True
    elif tag == 'FAIL_1':
        simplifyStrategy['START'] = False
        simplifyStrategy['FAILURE'] = True
        simplifyStrategy['REPLACE'] = False
        simplifyStrategy['SINGLE_REPLACE'] = True
    else:
        print('*** Error: SimplifyStrategy not recognized', file = sys.stderr)


def setRetryOnFailure(val):
    assert(isinstance(val, bool))
    simplifyStrategy['FULL_RETRY'] = val


def mergeAssociativeOpsOnBuild():
    return mergeAssociativeOps

def propagateCstOnBuild():
    return propagateCst

def bitExpEnable():
    return bitExp

def simplifyOnBuild():
    return SimplifyBuild

def useBuiltinExp():
    return builtinExp

def setMergeAssociativeOpsOnBuild(val):
    assert(isinstance(val, bool))
    global mergeAssociativeOps
    mergeAssociativeOps = val

def setPropagateCstOnBuild(val):
    assert(isinstance(val, bool))
    global propagateCst
    propagateCst = val

def setBitExpEnable(val):
    assert(isinstance(val, bool))
    global bitExp
    bitExp = val

def setSimplifyOnBuild(val):
    assert(isinstance(val, bool))
    global simplifyBuild
    simplifyBuild = val

#def setUseBuiltinExp(val):
#    assert(isinstance(val, bool))
#    global builtinExp
#    builtinExp = val
#

