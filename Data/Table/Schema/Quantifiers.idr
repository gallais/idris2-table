module Data.Table.Schema.Quantifiers

import Data.SnocList.Quantifiers
import public Data.Table.Schema.Data

namespace AllTypes
    public export
    data TypeHas : (p : Type -> Type) -> FieldSchema -> Type where
        TheTypeHas : p type -> TypeHas p (name :! type)

    export
    here : (0 _ : TypeHas (=== ty) v) -> Field (schema :< v) (v .fieldName) ty
    here (TheTypeHas eq) = Here (rewrite eq in Refl)

    public export
    AllTypes : (p : Type -> Type) -> Schema -> Type
    AllTypes p schema = All (TypeHas p) schema
