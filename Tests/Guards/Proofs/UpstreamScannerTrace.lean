/- Independent exact-byte audit, against cbc2ca9d / library parent 14eb6dba.
Capstone: Blueprint 7.7, contract admission before the global S3 induction.
No production source changes. The scanner-to-trace proposition holds on the
original upstream grammar for the seven-byte example, even though the stream
constructor admits two unseparated bare documents. -/
module
public import Tests.Guards.Proofs.UpstreamColonTrace
public import L4YAML.Proofs.Serialization.TokenEvents
public import L4YAML.Scanner.Scanner
public meta import Tests.Guards.Proofs.UpstreamColonTrace
-- The producer seals tokenEvents/go. This is the same reduction import
-- used by L4YAML.Proofs.Parser.StreamCompleteness; no definition changes.
import all L4YAML.Proofs.Serialization.TokenEvents
@[expose] public section Blanket

namespace L4YAML.Tests.Guards.UpstreamScannerTrace
open L4YAML
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Tests.Guards.UpstreamColonTrace

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

#guard input.toList = ['?', ' ', '-', '\n', ' ', ' ', ':']
#guard input.utf8ByteSize = 7

/-- Positive control: this version of the actual trace grammar admits empty input. -/
lemma empty_trace_control : TraceOf "" [] := traceOf_empty

/-- Direct kernel reduction binds the real scanner's result to no events. -/
lemma exact_scanner_events :
    (L4YAML.Scanner.scanFiltered input).map tokenEvents = .ok [] := by
  cbv

/-- This exact input's scanner-to-trace implication, for the actual returned ts. -/
lemma exact_original_scanner_trace_of_success
    (ts : Array (Positioned YamlToken))
    (hs : L4YAML.Scanner.scanFiltered input = .ok ts) :
    TraceOf input (tokenEvents ts) := by
  have h := exact_scanner_events
  rw [hs] at h
  have he : tokenEvents ts = [] := by
    simpa only [Except.map, Except.ok.injEq] using h
  rw [he]
  exact traceOf_seven_bytes

/-- The exact original-upstream S3 instance requested by the investigation. -/
lemma exact_original_scanner_trace :
    ∃ ts, L4YAML.Scanner.scanFiltered input = .ok ts ∧
      TraceOf input (tokenEvents ts) := by
  have h := exact_scanner_events
  cases hs : L4YAML.Scanner.scanFiltered input with
  | error e =>
    rw [hs] at h
    cases h
  | ok ts =>
    refine ⟨ts, rfl, ?_⟩
    exact exact_original_scanner_trace_of_success ts hs

#print axioms empty_trace_control
#print axioms exact_scanner_events
#print axioms exact_original_scanner_trace_of_success
#print axioms exact_original_scanner_trace

end L4YAML.Tests.Guards.UpstreamScannerTrace
end Blanket
