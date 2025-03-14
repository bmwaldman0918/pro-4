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

def InfiniteList.append {a : Type} (l : InfiniteList a) (l' : Option (InfiniteList a)) : InfiniteList a :=
  match l with
  | .bot =>
    match l' with
    | some l' => l'
    | none => l
  | .cons a as => .cons a (append as l')

def InfiniteList.appendElem {a : Type} (l : InfiniteList a) (l' : Option a) : InfiniteList a :=
  match l with
  | .bot =>
    match l' with
    | some l' => cons l' bot
    | none => bot
  | .cons a as => .cons a (appendElem as l')

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

-- def InfiniteList.get {X : Type} (idx : Nat) (l : Option (InfiniteList X)) : Option X :=
--   match l with
--   | none => none
--   | some l' =>
--     match l' with
--     | .cons x xs =>
--       match idx with
--       | .zero => some x
--       | .succ m => get m xs
--     | _ => none

-- Gets the element at IDX
def InfiniteList.get {X : Type} (idx : Nat) (l : InfiniteList X) : Option X :=
  match l with
  | .cons x xs =>
    match idx with
    | .zero => some x
    | .succ m => get m xs
  | _ => none

def InfiniteList.tail {X : Type} (l : InfiniteList X) : InfiniteList X :=
  match l with
  | .cons _ xs => xs
  | _ => bot

def InfiniteList.head {X : Type} (l : InfiniteList X) : Option X :=
  match l with
  | .cons x _ => some x
  | _ => none

def mem (i : Nat) (l : InfiniteList Nat) : Prop :=
  match l with
  | .cons x xs => x = i ∨ mem i xs
  | _ => False
