
# FarRP

FarRP is an arrowized FRP library for Idris which uses dependent types to
provide static guarantees. It is based on Neil Sculthorpe and Henrik Nilsson's
paper ["Safe Functional Reactive Programming through Dependent Types"](http://www.cs.rhul.ac.uk/home/ucac009/publications/safe-FRP-types.pdf).

## Contributing

Contributions in the form of pull requests, bug reports, and thoughts on how to
improve this library would be most appreciated. In particular there are several
open problems that could be worked on.

- Making stepSF total. Currently the case for SFLoop uses non-terminating
  recursion. This is probably the most pressing issue.

- Verifying that the implementation follows the semantics given in the paper.
  When implementing this system I didn't pay strict attention to the formal
  semantics, but it should be verified that these semantics are followed.

- Raising functions with pi types (e.g. (x : a) -> P x) to the SF level. This is
  a long term goal.

I should stress that bug reports would be most helpful, especially considering
how new this library is.

## Examples

Examples can be found in the examples/ directory. An example session of running
an example is given below.

```
> idris --build farrp.ipkg
Entering directory `./src'
Type checking ./FarRP/Time.idr
Type checking ./FarRP/SigVect.idr
Type checking ./FarRP/DecDesc.idr
Type checking ./FarRP/Core.idr
Type checking ./FarRP/Combinators.idr
Type checking ./FarRP.idr
Leaving directory `./src'

> cd examples
> idris average.idr -i ../src -o avg
> ./avg
1
1
2
1.5
3
2
4
2.5
5
3
^C
```

# License

Copyright (C) 2018 Taran Lynn <<taranlynn0@gmail.com>>

This library is licensed under the LGPLv3 (see LICENSE file).
