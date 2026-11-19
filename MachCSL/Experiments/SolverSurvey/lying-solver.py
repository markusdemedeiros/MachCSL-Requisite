#!/usr/bin/env python3
"""Deliberately invalid SMT oracle used only by replay rejection tests."""
import sys

sys.stdin.read()
print("unsat\n(h0)")
