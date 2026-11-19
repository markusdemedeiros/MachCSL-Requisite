#!/usr/bin/env python3
"""Deliberately corrupt assignment for the fail-closed replay regression."""
import sys
sys.stdin.read()
print('sat\n((r0 0) (r1 0))')
