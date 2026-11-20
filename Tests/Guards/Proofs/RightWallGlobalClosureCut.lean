/-
MathGraph Right-Wall global-closure cut (source-qualified proof, not closure).
Source: exact integrated corrected-grammar fork commit
ba12de17ff1339b6711fddd15f27b183d3ab7509.
Original foundation: nasa-jpl/L4YAML #359 head
57721b243c6f1bdd33e8d49c9aedd4f15e552c58.
Verification boundary: ONLY the implication from separately stated
bridges to the actual API-level theorem; the bridges are not discharged.
-/
module

public import L4YAML.Proofs.Serialization.ExecutableBoundary
public import L4YAML.Proofs.Serialization.ScannerShape
public import L4YAML.Proofs.Serialization.TraceOf.Document
public import L4YAML.Proofs.Serialization.TokenEvents

@[expose] public section Blanket

namespace L4YAML.Proofs.RightWallGlobalClosure

open L4YAML
open L4YAML.Proofs.Serialization
open L4YAML.Proofs.Serialization.TokenEvents (tokenEvents)
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.SerializationWellFormed

/-! A missing native S3 proof. Restricting to parser-accepted token arrays is
sufficient for the stated Group 7.7 forward direction. -/
def S3Accepted : Prop :=
  ∀ (source : String) (ts : Array (Positioned YamlToken))
    (raw : Array YamlDocument),
    Scanner.scanFiltered source = .ok ts →
    TokenParser.parseStream ts = .ok raw →
    TraceOf source (tokenEvents ts)

/-! Strong S4 and the property-relative alternative are explicitly
distinct. A valid annotation need not be the ONLY annotation. -/
def S4Unique : Prop :=
  ∀ (source : String) (ev₁ ev₂ : List Event),
    TraceOf source ev₁ → TraceOf source ev₂ → ev₁ = ev₂

def VerdictCoherentAccepted : Prop :=
  ∀ (source : String) (ev₁ ev₂ : List Event),
    (∃ docs, TokenParser.parseYaml source = .ok docs) →
    TraceOf source ev₁ → TraceOf source ev₂ →
    (SerializationWellFormed ev₁ ↔ SerializationWellFormed ev₂)

/-- An accepted source has a well-formed scanner event trace.
This part is ALREADY WARRANTED by the existing scanner+parser S5 lemma.
No extra assumption is needed here. -/
lemma accepted_has_wellformed_token_events (source : String)
    (hAccept : ∃ docs, TokenParser.parseYaml source = .ok docs) :
    ∃ ts, Scanner.scanFiltered source = .ok ts ∧
      SerializationWellFormed (tokenEvents ts) := by
  obtain ⟨ts, raw, hScan, hParse⟩ :=
    (parse_iff_executable_language source).mp hAccept
  have hChk : checkFrom {} (tokenEvents ts) = true :=
    ScannerShape.scanFiltered_parseStream_ok_checkFrom_full
      source ts raw hScan hParse
  exact ⟨ts, hScan, (serializationWellFormed_iff_check (tokenEvents ts)).mpr hChk⟩

/-- Strong S4 is one admissible bridge for global acceptance soundness.
S3 and S4 are ASSUMPTIONS here, not proven by this declaration. -/
theorem global_forward_via_trace_identity
    (hS3 : S3Accepted) (hS4 : S4Unique)
    (source : String)
    (hAccept : ∃ docs, TokenParser.parseYaml source = .ok docs) :
    TraceWellFormed source := by
  obtain ⟨ts, raw, hScan, hParse⟩ :=
    (parse_iff_executable_language source).mp hAccept
  have hEvent : TraceOf source (tokenEvents ts) :=
    hS3 source ts raw hScan hParse
  have hWF : SerializationWellFormed (tokenEvents ts) :=
    (serializationWellFormed_iff_check (tokenEvents ts)).mpr
      (ScannerShape.scanFiltered_parseStream_ok_checkFrom_full source ts raw hScan hParse)
  intro ev hTrace
  simpa [hS4 source ev (tokenEvents ts) hTrace hEvent] using hWF

/-- A property-relative lift can replace S4 literal equality for the
DECLARED acceptance requirement, if it can independently be proved. -/
theorem global_forward_via_verdict
    (hS3 : S3Accepted) (hV : VerdictCoherentAccepted)
    (source : String)
    (hAccept : ∃ docs, TokenParser.parseYaml source = .ok docs) :
    TraceWellFormed source := by
  obtain ⟨ts, raw, hScan, hParse⟩ :=
    (parse_iff_executable_language source).mp hAccept
  have hEvent : TraceOf source (tokenEvents ts) :=
    hS3 source ts raw hScan hParse
  have hWF : SerializationWellFormed (tokenEvents ts) :=
    (serializationWellFormed_iff_check (tokenEvents ts)).mpr
      (ScannerShape.scanFiltered_parseStream_ok_checkFrom_full source ts raw hScan hParse)
  intro ev hTrace
  exact (hV source ev (tokenEvents ts) hAccept hTrace hEvent).mpr hWF

/-!
The intended Group 7.7 biconditional, with its currently undeclared
ExactSurfaceLanguage supplied as an independent predicate.
The forward surface obligation and backward scanner/parser obligations
are NOT provided by the current source; encoding them explicitly stops
inferred local proof coverage from being mistaken for global closure.
-/
theorem global_group77_cut
    (ExactSurface : String → Prop)
    (hS3 : S3Accepted) (hVerdict : VerdictCoherentAccepted)
    (hSurfaceForward : ∀ source, InExecutableLanguage source → ExactSurface source)
    (hScanBackward : ∀ source, ExactSurface source → TraceWellFormed source →
      ∃ ts, Scanner.scanFiltered source = .ok ts)
    (hParseBackward : ∀ source ts,
      ExactSurface source → TraceWellFormed source →
      Scanner.scanFiltered source = .ok ts →
      ∃ raw, TokenParser.parseStream ts = .ok raw)
    (source : String) :
    (∃ docs, TokenParser.parseYaml source = .ok docs) ↔
      (ExactSurface source ∧ TraceWellFormed source) := by
  constructor
  · intro hAccept
    refine ⟨hSurfaceForward source ((parse_iff_executable_language source).mp hAccept),
      global_forward_via_verdict hS3 hVerdict source hAccept⟩
  · rintro ⟨hSurface, hTraces⟩
    obtain ⟨ts, hScan⟩ := hScanBackward source hSurface hTraces
    obtain ⟨raw, hParse⟩ := hParseBackward source ts hSurface hTraces hScan
    exact (parse_iff_executable_language source).mpr ⟨ts, raw, hScan, hParse⟩

#print axioms accepted_has_wellformed_token_events
#print axioms global_forward_via_trace_identity
#print axioms global_forward_via_verdict
#print axioms global_group77_cut

end L4YAML.Proofs.RightWallGlobalClosure
end Blanket
