data OrdinalType
    = ZeroOrdinal
    | SuccessorOrdinal
    | LimitOrdinal

class SystemOfNotation s where
    k :: s -> OrdinalType
    p :: s -> s
    q :: s -> (s -> s)

get_limit_pred :: (SystemOfNotation s) => s -> s
get_limit_pred n = get_limit_pred' (k n) n
    where get_limit_pred' ZeroOrdinal n      = n
          get_limit_pred' SuccessorOrdinal n = get_limit_pred (p n)
          get_limit_pred' LimitOrdinal n     = n

class SystemOfNotation s => UnivalentSystem s where
    leq :: s -> s -> Bool

