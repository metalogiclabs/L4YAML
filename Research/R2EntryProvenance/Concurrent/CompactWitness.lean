import Tests.AdversarialInstantiation
open Tests.AdversarialInstantiation
#eval P144Test.valueSlots "? ? a\n  : - b\n: c"
#eval P144Test.valueSlots "?\n  ? a\n  : - b\n: c"
#eval P144Test.valueSlots "? ? ? a\n    : - b\n  : c\n: d"
#eval P144Test.valueSlots "? a\n: - b"
#guard P144Test.valueSlots "? ? a\n  : - b\n: c" == [(true, 2, [0]), (true, 0, [])]
#guard P144Test.valueSlots "?\n  ? a\n  : - b\n: c" == [(true, 2, [0]), (true, 0, [])]
#guard P144Test.valueSlots "? ? ? a\n    : - b\n  : c\n: d" == [(true, 4, [0, 2]), (true, 2, [0]), (true, 0, [])]
#guard P144Test.valueSlots "? a\n: - b" == [(true, 0, [])]
