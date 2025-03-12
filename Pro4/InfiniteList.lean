inductive InfiniteList (t : Type) where
  -- | nil       : InfiniteList t
  | bot       : InfiniteList t
  | cons      : t → (InfiniteList t) → InfiniteList t

def InfiniteList.map {a b : Type} (f : a → b) (l : InfiniteList a) : InfiniteList b :=
  match l with
  -- | .nil       => .nil
  | .bot       => .bot
  | .cons a as => .cons (f a) (map f as)

def InfiniteList.take {a : Type} (l : InfiniteList a) (i : Nat) : InfiniteList a :=
  match i with
  | .zero => .bot
  | .succ i =>
    match l with
    | .cons a as => .cons a (take as i)
    | _ => l

def increasing (l : Option (InfiniteList Nat)) : Prop :=
  match l with
    | none => True
    | some l' =>
      match l' with
      -- | .nil => True
      | .bot => True
      -- | .cons _ .nil => True
      | .cons _ .bot => True
      | .cons x (.cons x' xs) => (x < x') ∧ increasing (some (.cons x' xs))

def InfiniteList.get {X : Type} (idx : Nat) (l : Option (InfiniteList X)) : Option X :=
  match l with
  | none => none
  | some l' =>
    match l' with
    | .cons x xs =>
      match idx with
      | .zero => some x
      | .succ m => get m xs
    | _ => none

def mem (i : Nat) (l : InfiniteList Nat) : Prop :=
  match l with
  | .cons x xs => x = i ∨ mem i xs
  | _ => False
