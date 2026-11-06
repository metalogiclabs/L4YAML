module

import DirectiveTrace
meta import DirectiveTrace

/-!
Fixed consumer contract, written before the proof body. Qualification is
governed by official CI receipts for the exact source commit.
The source witnesses and general conditional obstruction must have kernel-only
profiles; native runtime leaves are separately inspected below.
-/

open L4YAML
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open MathGraph.WholeSource.DirectiveTrace

example : TraceOf "%YAML 1.2\n---" [Event.beginDocument] := trace_one
example : TraceOf "%YAML 1.2\n%YAML 1.2\n---" [Event.beginDocument] := trace_two
example : SerializationWellFormed [Event.beginDocument] := trace_wellFormed

example : ∃ docs, TokenParser.parseYaml "%YAML 1.2\n---" = .ok docs :=
  Runtime.acceptance_one

example : ¬ ∃ docs, TokenParser.parseYaml "%YAML 1.2\n%YAML 1.2\n---" = .ok docs :=
  Runtime.rejection_two

example : ¬ (∀ input ev, TraceOf input ev → SerializationWellFormed ev →
    ∃ docs, TokenParser.parseYaml input = .ok docs) :=
  one_trace_source_completeness_refuted

example : ¬ ∃ P : List Event → Prop,
    ∀ input ev, TraceOf input ev →
      ((∃ docs, TokenParser.parseYaml input = .ok docs) ↔ P ev) :=
  no_event_predicate_characterizes_acceptance

#print axioms MathGraph.WholeSource.DirectiveTrace.trace_one
#print axioms MathGraph.WholeSource.DirectiveTrace.trace_two
#print axioms MathGraph.WholeSource.DirectiveTrace.trace_wellFormed
#print axioms MathGraph.WholeSource.DirectiveTrace.no_factorization_of_collision
#print axioms MathGraph.WholeSource.DirectiveTrace.no_event_predicate_of_conflicting_answers
#print axioms MathGraph.WholeSource.DirectiveTrace.Runtime.accepts_one
#print axioms MathGraph.WholeSource.DirectiveTrace.Runtime.rejects_two
#print axioms MathGraph.WholeSource.DirectiveTrace.Runtime.acceptance_one
#print axioms MathGraph.WholeSource.DirectiveTrace.Runtime.rejection_two
#print axioms MathGraph.WholeSource.DirectiveTrace.one_trace_source_completeness_refuted
#print axioms MathGraph.WholeSource.DirectiveTrace.no_event_predicate_characterizes_acceptance
