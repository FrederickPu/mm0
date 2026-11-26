import MM0.Parse

/-!
`mm0-lean check FILE.mm0`: parse and elaborate a `.mm0` file; exit 0 if it is
well formed, 1 otherwise (with the reason on stderr).
`mm0-lean dump FILE.mm0`: print the elaborated `MM0.Env`, one declaration per line.
-/

open MM0 MM0.Parse

def main (args : List String) : IO UInt32 := do
  match args with
  | [cmd, file] =>
    match ← (elabFileIO file).run with
    | .error e =>
      IO.eprintln e
      return 1
    | .ok (env, st) =>
      if cmd == "dump" then
        for (x, _) in st.sorts do IO.println s!"sort-name {x}"
        for t in st.terms do IO.println s!"term-name {t.name}"
        for x in st.thms.reverse do IO.println s!"thm-name {x}"
        for d in env do IO.println (reprStr d |>.replace "\n" " ")
      return 0
  | _ =>
    IO.eprintln "usage: mm0-lean (check|dump) FILE.mm0"
    return 2
