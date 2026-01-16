#!/usr/bin/env python3

from fractions import *
original = Fraction(3, 2048)
output = Fraction(1, 512)
expected = Fraction(1, 256)

d_original_output = abs(original - output)
d_original_expected = abs(original - expected)
print(f"distance({original}, {output}) = {d_original_output}")
print(f"distance({original}, {expected}) = {d_original_expected}")
if d_original_output < d_original_expected:
    print("output is closer")
if d_original_output > d_original_expected:
    print("expected is closer")

if d_original_output == d_original_expected:
    print("distances are equal")


