import Subject
def main : IO Unit := do
  let r ← IO.Process.output {cmd := "/bin/false"}
  IO.println s!"tool exit (ignored): {r.exitCode}"
