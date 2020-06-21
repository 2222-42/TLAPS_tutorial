# Practices

## In Proof

証明に関するプラクティス

### Function

Use currying function, functions of type [Nat -> [Nat -> S]] instead of [Nat \X Nat -> S] for TLAPS.

## Solver(Prover) Backgrounds

Proof Assistantに関するプラクティス

### Not Backward-compatibility

TLAPSが使っているProof Assistantのいずれも後方互換性はない(Isabelleは例外)から、以前はできた証明が今はできないという可能性がある。

その場合は、証明の中身を変えればよい。

#### 具体的な問題

cf: ` [tlaplus] TLAPS: problem with proof of GCD from TLA+ Hyperbook (chapter 11.2)`

> I don't think any proof assistant promises backward compatibility because that would severely restrict change. 

Proof Assistantは後方互換性がない。

だから、以前はできた証明が今はできなくなる可能性がある。

> The obligation falls into the theory of non-linear integer arithmetic, which is undecidable and for which SMT solvers implement heuristics. Unfortunately, these are quite brittle, in particular when quantifiers are involved as in this case (namely the definition of Divides). 

> none of them found the proof automatically, so we must break down the proof one level further and indicate the witness terms for the existential quantifier 

Nicholasが見つけた失敗例は、SMT Solverの発見法にとっては決定できない、非線形実数計算の理論に陥ったことに原因がある。

Nicholasの場合は、中に入っている量化子がもろく、それが原因で証明を発見できなかったのだから、証明を分割し、その量化子からWitness Termsを示すようにすればよい。

#### Isabelleが例外であるとは

> The mechanism that Isabelle/HOL has adopted with the Archive of Formal Proofs [1](https://www.isa-afp.org) is to collect major proof developments and run regression tests with every new release of the prover. When proofs fail, the Isabelle implementors assess whether they consider the change to be overall positive or if it breaks too many developments. In case the change is retained, maintainers of the collection (and/or the original author) fix the failing proofs so that they are kept up to date with new Isabelle releases.

Isabelleはリリースごとに主要な証明を集めて退行していないかをテストし、失敗した場合は実装者がその変更が全体への前進を進めるをチェックするから、上述のSMTのようなひどい後方互換性の欠損はない。

### Differences between Backgrounds

Zeno does not solve the following theorem, but CVC4 does.

```
THEOREM Transitive == 
    ASSUME 
        NEW X \in Nat,
        NEW Y \in Nat,
        NEW Z \in Nat,
        X > Y,
        Y > Z
        PROVE X > Z + 1
```

Keep the differences in your mind.
