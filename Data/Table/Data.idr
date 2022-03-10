module Data.Table.Data

import public Data.Table.Record
import public Data.Table.Schema

%default total

public export
Table : Schema -> Type
Table schema = SnocList (Record schema)

%name Table tbl
