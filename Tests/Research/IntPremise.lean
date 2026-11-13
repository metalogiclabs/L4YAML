import L4YAML.Proofs.Schema.SchemaResolution

/-!
Bounded research proof spike for nasa-jpl/L4YAML PR #302, Lean 4.35.0.
The universal integer conversion-success premise is proved below without `sorry`.
The additional exponent and digit-only mantissa lemmas are preparatory only;
the universal float premise and unconditional capstone are NOT proved here.
This file is not part of the production library or registered as a capstone.
-/

open L4YAML L4YAML.Schema L4YAML.Spec.CoreSchema

private lemma digit_same (c : Char) : asciiDigit c = c.isDigit := by
  rfl

private lemma nat_go_all (cs : List Char) :
    ∀ b : Bool, cs.all asciiDigit = true →
      isNatL.go b cs = (if cs.isEmpty then b else true) := by
  induction cs with
  | nil => intro b _; rfl
  | cons c cs ih =>
      intro b h
      have hc : asciiDigit c = true := (Bool.and_eq_true _ _).mp h |>.1
      have ht : cs.all asciiDigit = true := (Bool.and_eq_true _ _).mp h |>.2
      have hneq : c ≠ '_' := by
        intro heq
        subst c
        simp [asciiDigit] at hc
      have htail : isNatL.go true cs = true := by
        simpa using ih true ht
      simp [isNatL.go, hneq, ← digit_same, hc, htail]

private lemma nat_some (cs : List Char) (h : oneOrMore asciiDigit cs = true) :
    (toNatL? cs).isSome = true := by
  have hpair : cs.isEmpty = false ∧ cs.all asciiDigit = true := by
    simpa [oneOrMore, Bool.and_eq_true] using h
  have hnat : isNatL cs = true := by
    change isNatL.go false cs = true
    rw [nat_go_all cs false hpair.2]
    simp [hpair.1]
  simp [toNatL?, hnat]

private lemma hex_go_some (cs : List Char) (h : cs.all asciiHex = true) :
    ∀ acc : Int, (parseHex.go acc cs).isSome = true := by
  induction cs with
  | nil => intro acc; rfl
  | cons c cs ih =>
      intro acc
      have hc : asciiHex c = true := (Bool.and_eq_true _ _).mp h |>.1
      have ht : cs.all asciiHex = true := (Bool.and_eq_true _ _).mp h |>.2
      have hd : (('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f')) ∨
          ('A' ≤ c ∧ c ≤ 'F') := by
        simpa [asciiHex, asciiDigit, Bool.or_eq_true] using hc
      rcases hd with (hd | ha) | hA
      · simp [parseHex.go, hd, ih ht]
      · have hnotd : ¬ ('0' ≤ c ∧ c ≤ '9') := by
          intro hd
          have haNat : 97 ≤ c.val.toNat ∧ c.val.toNat ≤ 102 := ha
          have hdNat : 48 ≤ c.val.toNat ∧ c.val.toNat ≤ 57 := hd
          omega
        simp [parseHex.go, hnotd, ha, ih ht]
      · have hnotd : ¬ ('0' ≤ c ∧ c ≤ '9') := by
          intro hd
          have hANat : 65 ≤ c.val.toNat ∧ c.val.toNat ≤ 70 := hA
          have hdNat : 48 ≤ c.val.toNat ∧ c.val.toNat ≤ 57 := hd
          omega
        have hnota : ¬ ('a' ≤ c ∧ c ≤ 'f') := by
          intro ha
          have hANat : 65 ≤ c.val.toNat ∧ c.val.toNat ≤ 70 := hA
          have haNat : 97 ≤ c.val.toNat ∧ c.val.toNat ≤ 102 := ha
          omega
        simp [parseHex.go, hnotd, hnota, hA, ih ht]

private lemma oct_go_some (cs : List Char) (h : cs.all asciiOctal = true) :
    ∀ acc : Int, (parseOctal.go acc cs).isSome = true := by
  induction cs with
  | nil => intro acc; rfl
  | cons c cs ih =>
      intro acc
      have hc : asciiOctal c = true := (Bool.and_eq_true _ _).mp h |>.1
      have ht : cs.all asciiOctal = true := (Bool.and_eq_true _ _).mp h |>.2
      have hd : '0' ≤ c ∧ c ≤ '7' := by
        simpa [asciiOctal] using hc
      simp [parseOctal.go, hd, ih ht]

private lemma toInt_some_digits (cs : List Char)
    (h : oneOrMore asciiDigit cs = true) :
    (toIntL? cs).isSome = true := by
  cases cs with
  | nil => simp [oneOrMore] at h
  | cons c cs =>
      have hc : asciiDigit c = true := by
        have hsplit : (c :: cs).isEmpty = false ∧
            (c :: cs).all asciiDigit = true := by
          simpa [oneOrMore, Bool.and_eq_true] using h
        have hpair := hsplit.2
        exact (Bool.and_eq_true _ _).mp hpair |>.1
      have hminus : c ≠ '-' := by
        intro heq
        subst c
        simp [asciiDigit] at hc
      have hn := nat_some (c :: cs) h
      simpa [toIntL?, hminus] using hn

private lemma digit_not (c forbidden : Char) (h : asciiDigit c = true)
    (hf : asciiDigit forbidden = false) : c ≠ forbidden := by
  intro heq
  subst c
  simp [hf] at h

private lemma int_some_digits (cs : List Char)
    (h : oneOrMore asciiDigit cs = true) :
    (isIntL cs).isSome = true := by
  cases cs with
  | nil => simp [oneOrMore] at h
  | cons c rest =>
      have hn := toInt_some_digits (c :: rest) h
      have hc : asciiDigit c = true := by
        have ha : (c :: rest).all asciiDigit = true := by
          simpa [oneOrMore, Bool.and_eq_true] using h
        exact (Bool.and_eq_true _ _).mp ha |>.1
      have hcminus : c ≠ '-' := digit_not c '-' hc (by decide)
      have hcplus : c ≠ '+' := digit_not c '+' hc (by decide)
      cases rest with
      | nil => simpa [isIntL, splitSign, hcminus, hcplus] using hn
      | cons d ds =>
          have hd : asciiDigit d = true := by
            have ha : (c :: d :: ds).all asciiDigit = true := by
              simpa [oneOrMore, Bool.and_eq_true] using h
            have ht := (Bool.and_eq_true _ _).mp ha |>.2
            exact (Bool.and_eq_true _ _).mp ht |>.1
          have hdx : d ≠ 'x' := digit_not d 'x' hd (by decide)
          have hdX : d ≠ 'X' := digit_not d 'X' hd (by decide)
          have hdo : d ≠ 'o' := digit_not d 'o' hd (by decide)
          have hdO : d ≠ 'O' := digit_not d 'O' hd (by decide)
          by_cases hc0 : c = '0'
          · subst c
            simpa [isIntL, splitSign, hdx, hdX, hdo, hdO] using hn
          · simpa [isIntL, splitSign, hc0, hcminus, hcplus] using hn

private lemma splitSign_digits (cs : List Char)
    (h : oneOrMore asciiDigit cs = true) :
    splitSign cs = (false, cs) := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      have hc : asciiDigit c = true := by
        have ha : (c :: rest).all asciiDigit = true := by
          simpa [oneOrMore, Bool.and_eq_true] using h
        exact (Bool.and_eq_true _ _).mp ha |>.1
      have hm : c ≠ '-' := digit_not c '-' hc (by decide)
      have hp : c ≠ '+' := digit_not c '+' hc (by decide)
      simp [splitSign, hm, hp]

private lemma int_some_signed_digits (cs : List Char)
    (h : oneOrMore asciiDigit cs = true) :
    (isIntL ('+' :: cs)).isSome = true ∧
    (isIntL ('-' :: cs)).isSome = true := by
  have hs := splitSign_digits cs h
  have hi := int_some_digits cs h
  have hi' := hi
  simp only [isIntL, hs] at hi'
  constructor
  · simpa only [isIntL, splitSign] using hi'
  · simp only [isIntL, splitSign]
    split at hi' <;> simp_all [Option.isSome_map]

private lemma int_some_decimal (cs : List Char)
    (h : oneOrMore asciiDigit (withoutSign cs) = true) :
    (isIntL cs).isSome = true := by
  cases cs with
  | nil => simp [withoutSign, oneOrMore] at h
  | cons c rest =>
      by_cases hp : c = '+' 
      · subst c
        have hr : oneOrMore asciiDigit rest = true := by
          simpa [withoutSign] using h
        exact (int_some_signed_digits rest hr).1
      · by_cases hm : c = '-'
        · subst c
          have hr : oneOrMore asciiDigit rest = true := by
            simpa [withoutSign] using h
          exact (int_some_signed_digits rest hr).2
        · have hr : oneOrMore asciiDigit (c :: rest) = true := by
            simpa [withoutSign, hp, hm] using h
          exact int_some_digits (c :: rest) hr

private lemma int_some_hex (rest : List Char)
    (h : oneOrMore asciiHex rest = true) :
    (isIntL ('0' :: 'x' :: rest)).isSome = true := by
  have ha : rest.all asciiHex = true := by
    have hp : rest.isEmpty = false ∧ rest.all asciiHex = true := by
      simpa [oneOrMore, Bool.and_eq_true] using h
    exact hp.2
  have hr := hex_go_some rest ha 0
  simpa [isIntL, splitSign, Option.isSome_map] using hr

private lemma int_some_octal (rest : List Char)
    (h : oneOrMore asciiOctal rest = true) :
    (isIntL ('0' :: 'o' :: rest)).isSome = true := by
  have ha : rest.all asciiOctal = true := by
    have hp : rest.isEmpty = false ∧ rest.all asciiOctal = true := by
      simpa [oneOrMore, Bool.and_eq_true] using h
    exact hp.2
  have hr := oct_go_some rest ha 0
  simpa [isIntL, splitSign, Option.isSome_map] using hr

private lemma int_some_octal_match (cs : List Char)
    (h : (match cs with
      | '0' :: 'o' :: rest => oneOrMore asciiOctal rest
      | _ => false) = true) :
    (isIntL cs).isSome = true := by
  cases cs with
  | nil => simp at h
  | cons c tail =>
      by_cases hc : c = '0'
      · subst c
        cases tail with
        | nil => simp at h
        | cons d rest =>
            by_cases hd : d = 'o'
            · subst d
              exact int_some_octal rest (by simpa using h)
            · simp [hd] at h
      · simp [hc] at h

private lemma int_some_hex_match (cs : List Char)
    (h : (match cs with
      | '0' :: 'x' :: rest => oneOrMore asciiHex rest
      | _ => false) = true) :
    (isIntL cs).isSome = true := by
  cases cs with
  | nil => simp at h
  | cons c tail =>
      by_cases hc : c = '0'
      · subst c
        cases tail with
        | nil => simp at h
        | cons d rest =>
            by_cases hd : d = 'x'
            · subst d
              exact int_some_hex rest (by simpa using h)
            · simp [hd] at h
      · simp [hc] at h

private lemma int_some_of_integerSpelling (s : String)
    (h : integerSpelling s = true) :
    (isInt s).isSome = true := by
  have hor :
      ((oneOrMore asciiDigit (withoutSign s.toList) ||
        (match s.toList with
          | '0' :: 'o' :: rest => oneOrMore asciiOctal rest
          | _ => false)) ||
        (match s.toList with
          | '0' :: 'x' :: rest => oneOrMore asciiHex rest
          | _ => false)) = true := by
    exact h
  have hs : (isIntL s.toList).isSome = true := by
    rcases (Bool.or_eq_true _ _).mp hor with (hor' | hx)
    · rcases (Bool.or_eq_true _ _).mp hor' with (hd | ho)
      · exact int_some_decimal s.toList hd
      · exact int_some_octal_match s.toList ho
    · exact int_some_hex_match s.toList hx
  simpa [isInt, h] using hs

#print axioms int_some_of_integerSpelling

private lemma exponent_some_of_digits (cs : List Char)
    (h : oneOrMore asciiDigit (withoutSign cs) = true) :
    (parseExponentL? cs).isSome = true := by
  cases cs with
  | nil => simp [oneOrMore, withoutSign] at h
  | cons c rest =>
      by_cases hplus : c = '+' 
      · subst c
        have hr : oneOrMore asciiDigit rest = true := by
          simpa [withoutSign] using h
        have hn := nat_some rest hr
        simpa [parseExponentL?, splitSign] using hn
      · by_cases hminus : c = '-'
        · subst c
          have hr : oneOrMore asciiDigit rest = true := by
            simpa [withoutSign] using h
          have hn := nat_some rest hr
          simpa [parseExponentL?, splitSign] using hn
        · have hr : oneOrMore asciiDigit (c :: rest) = true := by
            simpa [withoutSign, hplus, hminus] using h
          have hn := nat_some (c :: rest) hr
          have hs := splitSign_digits (c :: rest) hr
          simpa [parseExponentL?, hs] using hn

private lemma digits_no_dot (cs : List Char)
    (h : cs.all asciiDigit = true) : '.' ∉ cs := by
  induction cs with
  | nil => simp
  | cons c tail ih =>
      have hc : asciiDigit c = true := (Bool.and_eq_true _ _).mp h |>.1
      have ht : tail.all asciiDigit = true := (Bool.and_eq_true _ _).mp h |>.2
      have hnd : c ≠ '.' := digit_not c '.' hc (by decide)
      have hdc : '.' ≠ c := Ne.symm hnd
      simp [hdc, ih ht]

private lemma mantissa_some_digits (cs : List Char)
    (h : oneOrMore asciiDigit cs = true) :
    (parseMantissaL? cs).isSome = true := by
  cases cs with
  | nil => simp [oneOrMore] at h
  | cons c rest =>
      have ha : (c :: rest).all asciiDigit = true := by
        have hp : (c :: rest).isEmpty = false ∧
            (c :: rest).all asciiDigit = true := by
          simpa [oneOrMore, Bool.and_eq_true] using h
        exact hp.2
      have hc : asciiDigit c = true := (Bool.and_eq_true _ _).mp ha |>.1
      have hnd : c ≠ '.' := digit_not c '.' hc (by decide)
      have hno := digits_no_dot (c :: rest) ha
      have hnrec : '.' ∉ rest := by
        intro hm
        exact hno (List.mem_cons_of_mem c hm)
      have hneqc : '.' ≠ c := Ne.symm hnd
      have hs1 : (c :: rest) ≠ ['0', '.'] := by
        intro heq
        simp [heq] at hno
      have hs2 : (c :: rest) ≠ ['0', '.', '0'] := by
        intro heq
        simp [heq] at hno
      have hsp1 : ¬(c = '0' ∧ rest = ['.']) := by
        intro hp
        exact hs1 (by simp [hp.1, hp.2])
      have hsp2 : ¬(c = '0' ∧ rest = ['.', '0']) := by
        intro hp
        exact hs2 (by simp [hp.1, hp.2])
      have hn := toInt_some_digits (c :: rest) h
      simpa [parseMantissaL?, hnd, hneqc, hnrec, hsp1, hsp2] using hn

