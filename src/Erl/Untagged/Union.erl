-module(erl_untagged_union@foreign).

-export([ isInt/1
        , isAtom/1
        , isBinary/1
        , isList/1
        , isLiteralAtom/2
        , isTuple1/1
        , isTuple2/1
        , isTuple3/1
        , isTuple4/1
        , isTuple5/1
        , isTuple6/1
        , isTuple7/1
        , isTuple8/1
        , isTuple9/1
        , isTuple10/1
        ]).

isInt(Int) when is_integer(Int) -> true;
isInt(_) -> false.

isBinary(Binary) when is_binary(Binary) -> true;
isBinary(_X) -> io:format(user, "x not binary ~p~n", [_X]), false.

isAtom(Atom) when is_atom(Atom) -> true;
isAtom(_) -> false.

isList(List) when is_list(List) -> true;
isList(_) -> false.

isLiteralAtom(Literal, Atom) when is_atom(Atom) ->
  case catch(binary_to_existing_atom(Literal)) of
      Atom -> true;
      _ -> false
  end;
isLiteralAtom(_, _) -> false.

isTuple1({_}) -> true;
isTuple1(_) -> false.

isTuple2({_, _}) -> true;
isTuple2(_) -> false.

isTuple3({_, _, _}) -> true;
isTuple3(_) -> false.

isTuple4({_, _, _, _}) -> true;
isTuple4(_) -> false.

isTuple5({_, _, _, _, _}) -> true;
isTuple5(_) -> false.

isTuple6({_, _, _, _, _, _}) -> true;
isTuple6(_) -> false.

isTuple7({_, _, _, _, _, _, _}) -> true;
isTuple7(_) -> false.

isTuple8({_, _, _, _, _, _, _, _}) -> true;
isTuple8(_) -> false.

isTuple9({_, _, _, _, _, _, _, _, _}) -> true;
isTuple9(_) -> false.

isTuple10({_, _, _, _, _, _, _, _, _, _}) -> true;
isTuple10(_) -> false.
