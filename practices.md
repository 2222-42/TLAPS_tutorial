# Practices

## Function

Use currying function, functions of type [Nat -> [Nat -> S]] instead of [Nat \X Nat -> S] for TLAPS.

## Differences between Backgrounds

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
