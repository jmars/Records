# Dependently Typed Extensible Records with Prototypal Inheritance

A 'dynamic' record system with strong correctness guarantees.

## Create
```idris
test : Record {lbl=String} ?testTy
test = [ "foo" := 1
       , "bar" := "a thing"
       , "bleh" := 1.2 ]
testTy = proof search
```

## Add
```idris
test2 : ?test2Ty
test2 = ("meh" := 10) :: test
test2Ty = proof search
```

## Remove
```idris
test3 : ?test3Ty
test3 = getProof $ "meh" - test
test3Ty = proof search
```

## Update
```idris
test4 : ?test4Ty
test4 = getProof $ ("meh" := 11) -: test2
test4Ty = proof search
```

## Inheritance
``` idris
test5 : ?test5Ty
test5 = test2 ++ test
test5Ty = proof search
```

Note: Proof search is not required if the record is not at the top scope level,
type inference will find the correct type inside functions or closures.
