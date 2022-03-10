module Data.Table.Schema

import Data.SnocList.Quantifiers
import public Data.Table.Schema.Data
import public Data.Table.Schema.Index
import public Data.Table.Schema.Quantifiers

%default total

public export
fromString : (name : String)
          -> {auto fld : Field schema name type}
          -> Field schema name type
fromString name = fld

public export
replace : (schema : Schema)
       -> Field schema name type
       -> FieldSchema
       -> Schema
replace (schema :< _) (Here _) newFS = schema :< newFS
replace (schema :< fs) (There fld) newFS = replace schema fld newFS :< fs

public export
update : (schema : Schema)
      -> Field schema name type
      -> Type
      -> Schema
update (schema :< fs) (Here _) newType = schema :< { fieldType := newType } fs
update (schema :< fs) (There fld) newType = update schema fld newType :< fs

public export
drop : (schema : Schema)
    -> Field schema name type
    -> Schema
drop (schema :< _) (Here _) = schema
drop (schema :< fs) (There fld) = drop schema fld :< fs
