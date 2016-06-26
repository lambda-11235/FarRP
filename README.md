
# FarRP

FarRP is a simple arrowized FRP library for Idris. It doesn't rely the IO or Eff
monads, so users can use it outside of these contexts. The library is based on
the state function (`SF`) datatype. Abstractly, an `SF a b` value can be thought
of as a function between two time varying values, that is as `(Time -> a) ->
(Time -> b). More pragmatically `SF` can be thought as a function that depends
on and changes with time. This can be seen in the `FarRP.Ideal` module and the
`stepSF` function.
``` idris
stepSF : SF a b -> DTime -> a -> (SF a b, b)
```
Here we see that the `SF` is producing a result of type `b` given an input of
type `b` and a time delta. It is also producing a new `SF` value. This shows the
core idea behind the FarFP library, that `SF` values are functions that vary
with time.

## Examples

Examples can be found in the examples/ directory.