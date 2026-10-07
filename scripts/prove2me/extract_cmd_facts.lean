/-
Stage 2b for the curve-symmetry upload (companion to the platform's
extract_sketch_info.lean, same elaboration loop): one JSON line per top-level
command of a file, with its syntax kind and exact span. The generator uses these
to compute, without pattern matching, the context (`namespace`/`section`/`end`
scopes, `open`, `variable`, `include`, `omit`, notations, `set_option`, local
attributes) active at each declaration, and to drop `#print` commands.

Usage: lake env lean --run p2m/extract_cmd_facts.lean <File.lean> > out.jsonl
Each line: {"kind":"cmd","syntaxKind":…,"start":P,"end":P}, P as in Stage 2.
-/
import Lean
open Lean Elab Parser

def posJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let pos := fm.toPosition p
  Json.mkObj [("line", toJson pos.line), ("col", toJson pos.column),
              ("offset", toJson p.byteIdx)]

unsafe def main (args : List String) : IO UInt32 := do
  let some fileName := args[0]?
    | do IO.eprintln "usage: lake env lean --run extract_cmd_facts.lean <File.lean>"
         return 1
  let input ← IO.FS.readFile (⟨fileName⟩ : System.FilePath)
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let cmdState := Command.mkState env messages {}
  let s ← IO.processCommands inputCtx parserState cmdState
  if s.commandState.messages.hasErrors then
    for msg in s.commandState.messages.toList do
      IO.eprintln (← msg.toString)
    return 1
  let fm := inputCtx.fileMap
  -- the header (imports) as its own fact
  if let (some hs, some he) := (header.raw.getPos?, header.raw.getTailPos?) then
    IO.println (Json.mkObj [("kind", Json.str "cmd"), ("syntaxKind", Json.str "header"),
      ("start", posJson fm hs), ("end", posJson fm he)]).compress
  for cmd in s.commands do
    let some cs := cmd.getPos? | continue
    let some ce := cmd.getTailPos? | continue
    IO.println (Json.mkObj [("kind", Json.str "cmd"), ("syntaxKind", Json.str cmd.getKind.toString),
      ("start", posJson fm cs), ("end", posJson fm ce)]).compress
  return 0
