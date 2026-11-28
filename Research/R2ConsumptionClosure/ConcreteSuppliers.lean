import Research.R2ConsumptionClosure.EntryValues
import Research.R2ContinuationContract.EntryRoutes

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.CharPredicates

namespace R2ConcreteSuppliers

-- Initializer and first actual value-token boundary, not a fabricated state.
def nthColon (input : String) (skip : Nat) : Option ScannerState :=
  let rec go (s : ScannerState) (fuel remaining : Nat) : Option ScannerState :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match scanNextToken s with
      | .ok (some next) =>
        if next.tokens.size > s.tokens.size && next.tokens.back?.any (fun t => t.val == .value)
        then match remaining with
          | 0 => some next
          | k + 1 => go next fuel k
        else go next fuel remaining
      | _ => none
  go ((ScannerState.mk' input).emit .streamStart) ((input.utf8ByteSize + 1) * 4) skip

def firstColon (input : String) : Option ScannerState := nthColon input 0

def afterFirstColon (input : String) : ScannerState :=
  (firstColon input).getD (ScannerState.mk' input)

lemma letterNode (n col : Nat) (ch : Char) (rest : List Char)
    (safe : isNsPlainSafe .flowOut ch) (notIndicator : ¬isIndicatorProp ch) :
    SBlockNode n .blockIn ⟨' ' :: ch :: '\n' :: rest, col⟩ ⟨rest, 0⟩ := by
  refine SBlockNode.flowInBlock n .blockIn _
    ⟨ch :: '\n' :: rest, col + 1⟩ ⟨'\n' :: rest, col + 2⟩ _ ?_ ?_ ?_
  · exact SSeparateLines.inline _ _ _
      (SSeparateInLine.whites _ _ (GPlus.mk _ _ _ (SSWhite.space _ col) (GStar.nil _)))
  · exact SFlowNode.content _ _ _ _ (SFlowContent.plain _ _ _ _
      (SNsPlainMultiLine.mk _ _ _ _ _
        (SNsPlainOneLine.mk _ _ _ _
          (SNsPlainFirst.nonIndicator _ ch _ (col + 1) safe notIndicator)
          (GStar.nil _)) (GStar.nil _)))
  · exact SSLComments.withComment _ _ _
      (SSBComment.noSep _ _ (SBComment.break _ _ (SBBreak.lf rest (col + 2))))
      (GStar.nil _)

lemma plainAKey (n col : Nat) (rest : List Char) :
    SBlockIndented n .blockOut ⟨' ' :: 'a' :: '\n' :: rest, col⟩ ⟨rest, 0⟩ :=
  SBlockIndented.node n .blockOut _ _
    (L4YAML.Proofs.NodeProduction.SBlockNode_blockIn_to_blockOut
      (letterNode (n + 1) col 'a' rest (by unfold isNsPlainSafe isNsChar; decide) (by decide)))

def input4 : String := "? ? ? a\n    : b\n: d\n"
def suffix4 : List Char := [':', ' ', 'b', '\n', ':', ' ', 'd', '\n']
def line4 : List Char := [' ', ' ', ' ', ' '] ++ suffix4
def q0_4 : SurfPos := ⟨['?', ' ', '?', ' ', '?', ' ', 'a', '\n'] ++ line4, 0⟩
def k0_4 : SurfPos := ⟨[' ', '?', ' ', '?', ' ', 'a', '\n'] ++ line4, 1⟩
def q1_4 : SurfPos := ⟨['?', ' ', '?', ' ', 'a', '\n'] ++ line4, 2⟩
def k1_4 : SurfPos := ⟨[' ', '?', ' ', 'a', '\n'] ++ line4, 3⟩
def q2_4 : SurfPos := ⟨['?', ' ', 'a', '\n'] ++ line4, 4⟩
def k2_4 : SurfPos := ⟨[' ', 'a', '\n'] ++ line4, 5⟩
def endKey4 : SurfPos := ⟨line4, 0⟩
def ind4 : SurfPos := ⟨suffix4, 4⟩
def value4 : SurfPos := ⟨[' ', 'b', '\n', ':', ' ', 'd', '\n'], 5⟩

example : q0_4.chars = input4.toList := by decide +kernel
-- Kernel reduction checks the initialized scanner actually reaches this park.
example : (firstColon input4).isSome = true := by decide +kernel
example : (afterFirstColon input4).offset = 13 ∧ (afterFirstColon input4).col = 5 := by decide +kernel
lemma marks4 : L4YAML.Proofs.RegisterWitness.markedCols (afterFirstColon input4) = [0, 2] := by decide +kernel

-- No free root-route assumption: this is the first-document `single` route.
-- No scannerDrop or implicitContinue is used to construct the context.
lemma actual_value_domain4 :
    ∀ e, SBlockNode 5 .blockIn value4 e →
      EntryValues (afterFirstColon input4) (SLYamlStream q0_4) e := by
  have root : ∀ v, SBlockMapEntry 0 q0_4 v →
      ∀ z, SCompactMapTail 0 v z → SLYamlStream q0_4 z :=
    fun v entry z tail =>
      (nodocMapRouteF (k := 0) (by rfl) (GStar.nil q0_4) (SIndent.zero q0_4)
        v entry z tail).close
  have rootKey := fun (e : SurfPos) (h : SBlockIndented 0 .blockOut k0_4 e) => entryStep_of_question (GLit.mk _ 0 : GLit '?' q0_4 k0_4) root h
  have entry1 := R2ContinuationPrimitives.compactEntryRoute rootKey
    (SIndent.succ 0 _ 1 q1_4 (SIndent.zero q1_4) : SIndent 1 k0_4 q1_4)
  have key1 := fun (e : SurfPos) (h : SBlockIndented 2 .blockOut k1_4 e) => entryStep_of_question (GLit.mk _ 2 : GLit '?' q1_4 k1_4) entry1 h
  have entry2 := R2ContinuationPrimitives.compactEntryRoute key1
    (SIndent.succ 0 _ 3 q2_4 (SIndent.zero q2_4) : SIndent 1 k1_4 q2_4)
  have key2 := entryStep_of_question (GLit.mk _ 4 : GLit '?' q2_4 k2_4) entry2
    (plainAKey 4 5 line4)
  have indent : SIndent 4 endKey4 ind4 := by
    exact SIndent.succ 3 _ 0 _ (SIndent.succ 2 _ 1 _ (SIndent.succ 1 _ 2 _
      (SIndent.succ 0 _ 3 _ (SIndent.zero ind4))))
  intro e node
  have supplied := colon_value_domain key2 indent (GLit.mk _ 4 : GLit ':' ind4 value4) e node
  simpa [EntryValues, columnCeiling, ValuesBelow, marks4] using supplied

def input6 : String := "? ? ? ? a\n      : b\n  : d\n: e\n"
def suffix6 : List Char := [':', ' ', 'b', '\n', ' ', ' ', ':', ' ', 'd', '\n', ':', ' ', 'e', '\n']
def line6 : List Char := [' ', ' ', ' ', ' ', ' ', ' '] ++ suffix6
def q0_6 : SurfPos := ⟨['?', ' ', '?', ' ', '?', ' ', '?', ' ', 'a', '\n'] ++ line6, 0⟩
def k0_6 : SurfPos := ⟨[' ', '?', ' ', '?', ' ', '?', ' ', 'a', '\n'] ++ line6, 1⟩
def q1_6 : SurfPos := ⟨['?', ' ', '?', ' ', '?', ' ', 'a', '\n'] ++ line6, 2⟩
def k1_6 : SurfPos := ⟨[' ', '?', ' ', '?', ' ', 'a', '\n'] ++ line6, 3⟩
def q2_6 : SurfPos := ⟨['?', ' ', '?', ' ', 'a', '\n'] ++ line6, 4⟩
def k2_6 : SurfPos := ⟨[' ', '?', ' ', 'a', '\n'] ++ line6, 5⟩
def q3_6 : SurfPos := ⟨['?', ' ', 'a', '\n'] ++ line6, 6⟩
def k3_6 : SurfPos := ⟨[' ', 'a', '\n'] ++ line6, 7⟩
def endKey6 : SurfPos := ⟨line6, 0⟩
def ind6 : SurfPos := ⟨suffix6, 6⟩
def value6 : SurfPos := ⟨[' ', 'b', '\n', ' ', ' ', ':', ' ', 'd', '\n', ':', ' ', 'e', '\n'], 7⟩
def secondState6 : ScannerState := (nthColon input6 1).getD (ScannerState.mk' input6)
def thirdState6 : ScannerState := (nthColon input6 2).getD (ScannerState.mk' input6)

example : q0_6.chars = input6.toList := by decide +kernel
example : (firstColon input6).isSome = true := by decide +kernel
example : (afterFirstColon input6).offset = 17 ∧ (afterFirstColon input6).col = 7 := by decide +kernel
example : (afterFirstColon input4).input.toList.drop (afterFirstColon input4).offset = value4.chars := by decide +kernel
example : (afterFirstColon input6).input.toList.drop (afterFirstColon input6).offset = value6.chars := by decide +kernel
lemma marks6 : L4YAML.Proofs.RegisterWitness.markedCols (afterFirstColon input6) = [0, 2, 4] := by decide +kernel
lemma marks6second : L4YAML.Proofs.RegisterWitness.markedCols secondState6 = [0] := by decide +kernel
lemma marks6third : L4YAML.Proofs.RegisterWitness.markedCols thirdState6 = [] := by decide +kernel
example : secondState6.offset = 23 ∧ secondState6.col = 3 := by decide +kernel
example : thirdState6.offset = 27 ∧ thirdState6.col = 1 := by decide +kernel

lemma actual_value_domain6 :
    ∀ e, SBlockNode 7 .blockIn value6 e →
      EntryValues (afterFirstColon input6) (SLYamlStream q0_6) e := by
  have root : ∀ v, SBlockMapEntry 0 q0_6 v →
      ∀ z, SCompactMapTail 0 v z → SLYamlStream q0_6 z :=
    fun v entry z tail =>
      (nodocMapRouteF (k := 0) (by rfl) (GStar.nil q0_6) (SIndent.zero q0_6)
        v entry z tail).close
  have rootKey := fun (e : SurfPos) (h : SBlockIndented 0 .blockOut k0_6 e) =>
    entryStep_of_question (GLit.mk _ 0 : GLit '?' q0_6 k0_6) root h
  have entry1 := R2ContinuationPrimitives.compactEntryRoute rootKey
    (SIndent.succ 0 _ 1 q1_6 (SIndent.zero q1_6) : SIndent 1 k0_6 q1_6)
  have key1 := fun (e : SurfPos) (h : SBlockIndented 2 .blockOut k1_6 e) =>
    entryStep_of_question (GLit.mk _ 2 : GLit '?' q1_6 k1_6) entry1 h
  have entry2 := R2ContinuationPrimitives.compactEntryRoute key1
    (SIndent.succ 0 _ 3 q2_6 (SIndent.zero q2_6) : SIndent 1 k1_6 q2_6)
  have key2 := fun (e : SurfPos) (h : SBlockIndented 4 .blockOut k2_6 e) =>
    entryStep_of_question (GLit.mk _ 4 : GLit '?' q2_6 k2_6) entry2 h
  have entry3 := R2ContinuationPrimitives.compactEntryRoute key2
    (SIndent.succ 0 _ 5 q3_6 (SIndent.zero q3_6) : SIndent 1 k2_6 q3_6)
  have key3 := entryStep_of_question (GLit.mk _ 6 : GLit '?' q3_6 k3_6) entry3
    (plainAKey 6 7 line6)
  have indent : SIndent 6 endKey6 ind6 := by
    exact SIndent.succ 5 _ 0 _ (SIndent.succ 4 _ 1 _ (SIndent.succ 3 _ 2 _
      (SIndent.succ 2 _ 3 _ (SIndent.succ 1 _ 4 _
        (SIndent.succ 0 _ 5 _ (SIndent.zero ind6))))))
  intro e node
  have supplied := colon_value_domain key3 indent (GLit.mk _ 6 : GLit ':' ind6 value6) e node
  simpa [EntryValues, columnCeiling, ValuesBelow, marks6] using supplied

-- Execute the real mixed grammar route, including omission of column 4
-- after column 6's value, then consumption at column 2 and at root 0.
lemma actual_6_2_0_consumption : SLYamlStream q0_6 ⟨[], 0⟩ := by
  let middle : List Char := [' ', ' ', ':', ' ', 'd', '\n', ':', ' ', 'e', '\n']
  have bNode := letterNode 7 7 'b' middle (by unfold isNsPlainSafe isNsChar; decide) (by decide)
  have afterB := actual_value_domain6 ⟨middle, 0⟩ bNode
  have ind2 : SIndent 2 ⟨middle, 0⟩ ⟨[':', ' ', 'd', '\n', ':', ' ', 'e', '\n'], 2⟩ :=
    SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero _))
  have colon2 : GLit ':' ⟨[':', ' ', 'd', '\n', ':', ' ', 'e', '\n'], 2⟩
      ⟨[' ', 'd', '\n', ':', ' ', 'e', '\n'], 3⟩ := GLit.mk _ 2
  have dNode := letterNode 3 3 'd' [':', ' ', 'e', '\n']
    (by unfold isNsPlainSafe isNsChar; decide) (by decide)
  have afterD : EntryValues secondState6 (SLYamlStream q0_6) ⟨[':', ' ', 'e', '\n'], 0⟩ :=
    EntryValues.consume afterB (by simp [marks6])
      (by intro x hx; simp only [marks6second, List.mem_singleton] at hx; subst x; simp [marks6])
      (by intro x hx; simp only [marks6second, List.mem_singleton] at hx; omega)
      ind2 colon2 (SBlockIndented.node 2 .blockOut _ _
        (L4YAML.Proofs.NodeProduction.SBlockNode_blockIn_to_blockOut dNode))
  have eNode := letterNode 1 1 'e' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide)
  have afterE : EntryValues thirdState6 (SLYamlStream q0_6) ⟨[], 0⟩ :=
    EntryValues.consume afterD (by simp [marks6second])
      (by simp [marks6third]) (by simp [marks6third])
      (SIndent.zero _) (GLit.mk _ 0) (SBlockIndented.node 0 .blockOut _ _
        (L4YAML.Proofs.NodeProduction.SBlockNode_blockIn_to_blockOut eNode))
  exact ValuesBelow.close afterE

#guard (L4YAML.TokenParser.parseYaml input4).isOk
#guard (L4YAML.TokenParser.parseYaml input6).isOk

#print axioms actual_value_domain6
#print axioms actual_6_2_0_consumption

#print axioms actual_value_domain4

end R2ConcreteSuppliers
