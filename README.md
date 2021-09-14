Immutable Size-Indexed Arrays
=====

This package provides an immutable array type which tracks/enforces its length.

This package's intent is to provide a [vector](https://hackage.haskell.org/package/vector)-like experience for Idris2 users along with stronger gurantees about how arrays match.

The compiler isn't quite there when it comes to tooling to do fusion, the basic %transform lacks the expressiveness and/or stages required for fusion. As tooling improves so will this package. The consequence of lacking fusion is that chained operations on arrays will do more copying that neccesary since they're immutable.

It's possible this package will become a front for a non-sized version of arrays but it is starting as sized. If you need non-sized arrays in the mean time, Idris comes with IOArray.

Version
-------

This package follows [Haskell PVP](https://pvp.haskell.org/) which is distinct from [SEMVER](https://semver.org/) in that when examining `1.2.3`, `1.2`  is the Major Version rather than `1`.
