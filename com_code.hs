-- Systems of notation

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

-- Examples

type OmegaTwoPlusOne = Int

instance SystemOfNotation OmegaTwoPlusOne where
    k n
       | n == 0    = LimitOrdinal      -- omega.2
       | n == 1    = LimitOrdinal      -- omega
       | n == 2    = ZeroOrdinal       -- 0
       | otherwise = SuccessorOrdinal  -- even: n; odd: omega + n
    p n
       | n > 2     = n - 2
       | otherwise = error("Predeccessor undefined")
    q n
       | n == 0    = (\m -> (2 * m) + 3)
       | n == 1    = (\m -> (2 * m) + 2)
       | otherwise = error("Limit function undefined")

instance UnivalentSystem OmegaTwoPlusOne where
    leq m n
        | n == m                                   = True
        | n == 0                                   = True
        | n == 1 && m > 0              && (even m) = True
        |           m == 2                         = True
        | n > 2  && m > 2  && (odd n)  && (odd m)  = m <= n
        | n > 2  && m > 2  && (odd n)  && (even m) = True
        | n > 2  && m > 2  && (even n) && (even m) = m <= n
        | otherwise                                = False
