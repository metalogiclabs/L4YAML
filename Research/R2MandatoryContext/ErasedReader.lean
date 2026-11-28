import Research.R2MandatoryContext.Births

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.PendingKeySound
open R2JointFrames

-- Expected rejection: erase the actual same-level question reader's semantic
-- context to its finished-stream projection, retaining every other premise.
example {s t : ScannerState} {P : SurfPos → Prop} {land q next : SurfPos}
    (step : scanKey s = .ok t) (flow : s.inFlow = false)
    (slots : SlotsOk s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s) (same : s.currentIndent = (s.col : Int))
    (context : Context s P land)
    (indent : SIndent s.col land q) (literal : GLit '?' q next) :
    Slot t P s.col .blockOut next :=
  R2MandatoryContext.actual_same_question step flow slots mono base same context.close indent literal
