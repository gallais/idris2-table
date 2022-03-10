module Data.Table.Schema.Data

import Data.SnocList
import Data.SnocList.Quantifiers

%default total

infix 10 :!

public export
record FieldSchema where
  constructor (:!)
  fieldName : String
  fieldType : Type

%name FieldSchema fs

public export
Schema : Type
Schema = SnocList FieldSchema

%name Schema schema

public export
names : Schema -> SnocList String
names = map fieldName

public export
types : Schema -> SnocList Type
types = map fieldType

public export
Field : (schema : Schema) -> (name : String) -> (type : Type) -> Type
Field schema name type = Any ((name :! type) ===) schema

%name Field fld
