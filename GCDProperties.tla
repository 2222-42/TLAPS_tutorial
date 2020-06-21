--------------------------- MODULE GCDProperties ---------------------------

EXTENDS Integers, FiniteSets, TLAPS, NaturalsInduction

Divides(p, n) == \E q \in Int : n = p * q
 
DivisorsOf(n) == {p \in Int : Divides(p, n)}
 
SetMax(S) ==  CHOOSE i \in S : \A j \in S : i >= j
 
GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

THEOREM GCD1 == \A m \in Nat \ {0} : GCD(m, m) = m
    <1> SUFFICES ASSUME NEW m \in Nat \ {0}
                 PROVE GCD(m, m) = m
        OBVIOUS
    <1>1 Divides(m, m)
        BY DEF Divides
    <1>2 \A i \in Nat : Divides(i, m) => (i =< m)
        BY DEF Divides
    <1> QED
        BY <1>1, <1>2 DEF GCD, SetMax, DivisorsOf

THEOREM GCD2 == \A m, n \in Nat \ {0} : GCD(m, n) = GCD(n, m)
    BY DEF GCD

THEOREM GCD3 == \A m, n \in Nat \ {0} : (n > m) => (GCD(m, n) = GCD(m, n-m))
    <1> SUFFICES ASSUME NEW m \in Nat \ {0},
                        NEW n \in Nat \ {0},
                        n > m
                 PROVE  GCD(m, n) = GCD(m, n-m)
        OBVIOUS
(* 
         PROVE  \A i \in Int :
          (\E q \in Int : m = i * q) /\ (\E q \in Int : n = i * q)
          <=> (\E q \in Int : m = i * q) /\ (\E q \in Int : n - m = i * q) 
*)
    <1>1 ASSUME NEW i \in Int, NEW q \in Int, m = i*q, NEW r \in Int, n = i*r
         PROVE \E z \in Int : n - m = i*z
         <2>1 r-q \in Int /\ n-m = i*(r-q)
            BY <1>1
            <2> QED BY <2>1
    <1>2 ASSUME NEW i \in Int, NEW q \in Int, m = i*q, NEW r \in Int, n-m = i*r
         PROVE \E z \in Int : n = i*z
         <2>1 r+q \in Int /\ n = i*(r+q)
            BY <1>2
         <2> QED BY <2>1
    <1> QED
        BY <1>1, <1>2 DEF GCD, SetMax, DivisorsOf, Divides

(* to prove with separate lemma *)

THEOREM CommonDivisorsWithDifference == \A m, n \in Nat \ {0} : 
                                        \A i \in Int : (n > m) =>
                                                                    (Divides(i, m) /\ Divides(i, n) <=> Divides(i, m) /\ Divides(i, n -m))
    <1> SUFFICES ASSUME NEW m \in Nat \ {0},
                        NEW n \in Nat \ {0},
                        NEW i \in Int,
                        n > m
                 PROVE (Divides(i, m) /\ Divides(i, n) <=> Divides(i, m) /\ Divides(i, n - m))
    <1>1 ASSUME NEW q \in Int, m = i*q, NEW r \in Int, n = i*r
         PROVE Divides(i, n - m)
         <2> r-q \in Int /\ n-m = i*(r-q)
            BY <1>1
         <2> QED BY DEF Divides
    <1>2 ASSUME NEW q \in Int, m = i*q, NEW r \in Int, n-m = i*r
         PROVE Divides(i, n)
         <2>1 r+q \in Int /\ n = i*(r+q)
            BY <1>2
         <2> QED BY <2>1 DEF Divides
     <1> QED BY <1>1, <1>2 DEF Divides
     
THEOREM GCD3_other == \A m, n \in Nat \ {0} : (n > m) => (GCD(m, n) = GCD(m, n-m))
    <1> SUFFICES ASSUME NEW m \in Nat \ {0},
                        NEW n \in Nat \ {0},
                        n > m
                 PROVE  GCD(m, n) = GCD(m, n-m)
        OBVIOUS
(*
ASSUME NEW CONSTANT m \in Nat \ {0},
       NEW CONSTANT n \in Nat \ {0},
       n > m 
PROVE  (CHOOSE i \in
                 {p \in Int : \E q \in Int : m = p * q}
                 \cap {p \in Int : \E q \in Int : n = p * q} :
          \A j
             \in {p \in Int : \E q \in Int : m = p * q}
                 \cap {p \in Int : \E q \in Int : n = p * q} :
             i >= j)
       = (CHOOSE i \in
                   {p \in Int : \E q \in Int : m = p * q}
                   \cap {p \in Int : \E q \in Int : n - m = p * q} :
            \A j
               \in {p \in Int : \E q \in Int : m = p * q}
                   \cap {p \in Int : \E q \in Int : n - m = p * q} :
               i >= j)
*)
     <1> CommonDivisorsWithDifference BY CommonDivisorsWithDifference DEF Divides
    <1> QED
        BY DEF GCD, SetMax, DivisorsOf
        
=============================================================================
