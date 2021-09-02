{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "erl-untagged"
, dependencies =
  [ "erl-atom"
  , "erl-binary"
  , "erl-lists"
  , "erl-tuples"
  , "debug"
  , "foreign"
  , "typelevel-prelude"
  , "maybe"
  , "partial"
  , "prelude"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
, backend = "purerl"
}
