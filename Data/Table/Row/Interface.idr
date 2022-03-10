module Data.Table.Row.Interface

import Data.Nat
import Data.DPair
import Data.SnocList
import Data.SnocList.Quantifiers

import public Data.Table.Data
import public Data.Table.Row.HasRows

public export
concatHasRows : (0 tbl1 : Table schema)
             -> (hasRows1 : HasRows tbl1 n1)
             => (0 tbl2 : Table schema)
             -> (hasRows2 : HasRows tbl2 n2)
             => HasRows (tbl1 ++ tbl2) (n1 + n2)
concatHasRows tbl1 [<] {hasRows2 = EmptyTable} =
    replace {p = HasRows _} (sym $ plusZeroRightNeutral _) $
    hasRows1
concatHasRows tbl1 (tbl2 :< rec) {hasRows2 = SnocTable hasRows} =
    replace {p = HasRows _} (plusSuccRightSucc _ _) $
    SnocTable (concatHasRows tbl1 tbl2)

-- "Functor"

namespace SnocList

    public export
    mapPreservesLength : HasRows tbl n => HasRows tbl (length (map f tbl))
    mapPreservesLength @{EmptyTable} = EmptyTable
    mapPreservesLength @{SnocTable _} = SnocTable mapPreservesLength

namespace Table

    public export
    mapPreservesLength : HasRows tbl n => HasRows (map f tbl) n
    mapPreservesLength @{EmptyTable} = EmptyTable
    mapPreservesLength @{SnocTable _} = SnocTable Table.mapPreservesLength

-- "Foldable"

public export
pureHasRows : HasRows (pure rec) 1
pureHasRows = SnocTable EmptyTable

public export
bindHasRows : (tbl : Table schema1)
           -> (fHasRows : (rec : Record schema1) -> (Exists (HasRows (f rec))))
           -> HasRows (tbl >>= f) (sum $ map (\rec => (fHasRows rec).fst) tbl)
bindHasRows [<] fHasRows = EmptyTable
bindHasRows (tbl :< rec) fHasRows = concatHasRows (tbl >>= f) @{bindHasRows _ _} (f rec) @{(fHasRows _).snd}

namespace HasRows
    public export
    (>>=) : (tbl : Table schema1)
         -> (fHasRows : (rec : Record schema1) -> (Exists (HasRows (f rec))))
         -> HasRows (tbl >>= f) (sum $ map (\rec => (fHasRows rec).fst) tbl)
    (>>=) = bindHasRows

public export
bindConstHasRows : (0 tbl : Table schema1)
                -> HasRows tbl m
                => (fHasRows : (0 rec : Record schema1) -> HasRows (f rec) n)
                -> HasRows (tbl >>= f) (m * n)
bindConstHasRows [<] @{EmptyTable} fHasRows = EmptyTable
bindConstHasRows {m = S m} (tbl :< rec) @{SnocTable _} fHasRows =
    replace {p = HasRows _} (plusCommutative _ _) $
    concatHasRows (tbl >>= f) @{bindConstHasRows _ fHasRows} (f rec) @{fHasRows rec}

namespace HasRowsConst
    public export
    (>>=) : (0 tbl : Table schema1)
         -> HasRows tbl m
         => (fHasRows : (0 rec : Record schema1) -> HasRows (f rec) n)
         -> HasRows (tbl >>= f) (m * n)
    (>>=) = bindConstHasRows
