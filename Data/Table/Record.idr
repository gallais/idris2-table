module Data.Table.Record

import Data.SnocList.Quantifiers
import public Data.Table.Schema

%default total

public export
Record : Schema -> Type
Record = All fieldType

%name Record rec

public export
value : Field schema name type
     -> Record schema
     -> type
value (Here Refl) (rec :< x) = x
value (There fld) (rec :< x) = value fld rec

public export
replaceField : (fld : Field schema name type)
            -> (0 newName : String)
            -> newType
            -> Record schema
            -> Record (replace schema fld (newName :! newType))
replaceField (Here Refl) newName x (rec :< _) = rec :< x
replaceField (There fld) newName x (rec :< y) = replaceField fld newName x rec :< y

public export
setField : (fld : Field schema name type)
        -> newType
        -> Record schema
        -> Record (update schema fld newType)
setField (Here Refl) x (rec :< _) = rec :< x
setField (There fld) x (rec :< y) = setField fld x rec :< y

public export
updateField : (fld : Field schema name type)
           -> (type -> newType)
           -> Record schema
           -> Record (update schema fld newType)
updateField fld f rec = setField fld (f $ value fld rec) rec

public export
dropField : (fld : Field schema name type)
         -> Record schema
         -> Record (drop schema fld)
dropField (Here _) (rec :< x) = rec
dropField (There fld) (rec :< x) = dropField fld rec :< x

public export
AllTypes Eq schema => Eq (Record schema) where
    ([<] == [<]) @{[<]} = True
    ((r :< x) == (s :< y)) @{_ :< TheTypeHas _} = x == y && delay (r == s)

%hint
public export
allTypesOrdEq : AllTypes Ord schema => AllTypes Eq schema
allTypesOrdEq @{[<]} = [<]
allTypesOrdEq @{_ :< TheTypeHas _} = %search :< %search

public export
AllTypes Ord schema => Ord (Record schema) where
    compare [<] [<] = EQ
    compare @{_ :< TheTypeHas _} (r :< x) (s :< y) = compare (r, x) (s, y)

public export
byField : Field schema name type
       -> Ord type
       => Eq (Record schema)
       => Ord (Record schema)
byField fld = ByField
  where
    [ByField] Ord (Record schema) where
        compare = compare `on` value fld
