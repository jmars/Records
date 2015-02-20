module Data.Record

namespace Record

  infix 5 :=
  infix 5 -:

  -- A record field is some label type paired with a value. := just
  -- gives a nicer syntax than tuples for this....

  data Field : lbl -> Type -> Type where
        (:=) : (field_label : lbl) -> 
               (value : b) -> Field field_label b

  -- Then a record is essentially a heterogeneous list where everything
  -- is labelled.
  data Record : List (lbl, Type) -> Type where
       Nil : Record {lbl} []
       (::) : Field lbl a -> Record xs -> Record ((lbl, a) :: xs)

  -- FieldType 'lbl rec ty 
  -- is a predicate stating that the label 'lbl in record with index
  -- rec has type ty.

  data FieldType : (field : lbl) -> Type -> List (lbl, Type) -> Type where
    First : FieldType field ty ((field, ty) :: xs)
    Later : FieldType field t xs -> FieldType field t (a :: xs)

  -- To extract a field from the record, we need the field label, a
  -- record, and a proof that the field is valid for the type we want.

  get' : Record xs -> FieldType field t xs -> t
  get' ((_ := val) :: xs) First = val
  get' (_ :: xs) (Later y) = get' xs y

  (.) : Record {lbl} xs -> (field : lbl) -> { auto prf : FieldType field t xs} -> t
  (.) rec f {prf} = get' rec prf

  -- Delete a field

  delete' : FieldType field t zs -> Record {lbl} zs -> (m ** Record {lbl} m)
  delete' First (x :: xs) = (_ ** xs)
  delete' (Later y) (x :: xs) with (delete' y xs)
    | (ts ** ys) = (_ :: ts ** x :: ys)

  (-) : (field : lbl) -> Record {lbl} xs ->
        { auto prf : FieldType field t xs } ->
        (m ** Record {lbl} m)
  (-) f rec {prf} = delete' prf rec

  -- Combine two records (prototypal inheritance)

  (++) : Record {lbl} xs -> Record {lbl} ys -> Record (xs ++ ys)
  (++) []        ys = ys
  (++) (x :: xs) ys = x :: (xs ++ ys)

  -- Update a field, possibly changing the type

  update' : Record {lbl} xs -> FieldType field t xs -> Field field a -> (m ** Record {lbl} m)
  update' (x :: xs) First v = (_ ** v :: xs)
  update' (x :: xs) (Later y) v with (update' xs y v)
    | (ts ** ys) = (_ :: ts ** x :: ys)

  (-:) : Field field t -> Record {lbl} xs ->
         { auto prf : FieldType field t xs } ->
         (m ** Record {lbl} m)
  (-:) f rec {prf} = update' rec prf f
