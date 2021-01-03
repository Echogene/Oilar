Inductive Foo : Set := e1.
Inductive Bar : Set := e2.

Definition Foobar: Type := Foo + Bar.

Print Foobar.

Definition foo: Foobar := inl e1.
Definition bar: Foobar := inr e2.

Definition lol (foobar: Foobar): bool :=
match foobar with
| inl _ => false
| inr _ => true
end.

Definition rofl {A B} (foobar: A + B): Type :=
match foobar with
| inl _ => A
| inr _ => B
end.

Compute rofl bar.
