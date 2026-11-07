module
public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition
public meta import Lean

namespace MathGraph.NormativeComments
@[expose] public section
open L4YAML

-- Four legacy public paths must agree on acceptance, including comment preservation.
def paths (s : String) : List Bool := [
  (Scanner.scan s).isOk,
  (Scanner.scanWithComments s).isOk,
  (TokenParser.parseYaml s).isOk,
  (TokenParser.parseYamlWithComments s).isOk]

def contexts (body : String) : List String := [
  "#" ++ body, "#" ++ body ++ "\n", "#" ++ body ++ "\r\n",
  "%YAML 1.2 #" ++ body ++ "\n---\n",
  "%TAG !e! tag:example.org,2026: #" ++ body ++ "\n---\n",
  "%RESERVED parameter #" ++ body ++ "\n---\n",
  "a #" ++ body ++ "\n", "[a, #" ++ body ++ "\n b]\n",
  "| #" ++ body ++ "\n  a\n", "> #" ++ body ++ "\n  a\n",
  "---\na\n... #" ++ body ++ "\n"]

-- All forbidden C0 code points, DEL, C1 boundaries, BOM and noncharacters.
def forbidden : List Nat :=
  (List.range 32).filter (fun n => n != 9 && n != 10 && n != 13) ++
    [0x7f, 0x80, 0x84, 0x86, 0x9f, 0xfeff, 0xfffe, 0xffff]

#guard forbidden.all fun n => (contexts (String.singleton (Char.ofNat n))).all
  fun s => (paths s).all (! ·)
#guard (["", "a", "\t", "é", "λ", "😀", "\u0085", "\u00a0", "\ufffd"] : List String).all
  fun body => (contexts body).all fun s => (paths s).all id
-- Raw quoted nb-json and decoded escaped controls are separate from comments.
#guard (["\"\\x01\"", "\"#\\x01\"", "\"\u007f\"", "\"\u0080\"", "\"\uFEFF\""] : List String).all
  fun s => (paths s).all id

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma public_rejects_minimal : (TokenParser.parseYaml "#\x01").isOk = false := by
  decide +kernel

#check public_rejects_minimal
#print axioms public_rejects_minimal
open Lean Elab Command in
run_cmd do
  let axs ← collectAxioms ``public_rejects_minimal
  unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
    throwError "Unexpected axioms: {axs}"
  logInfo m!"QUALIFIED_AXIOMS public_rejects_minimal: {axs}"
end MathGraph.NormativeComments
