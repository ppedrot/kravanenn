/// A dumbed-down version of Cow that has no requirements on its type parameters.
pub enum Cow<'a, B, O> where B: ?Sized + 'a {
    Borrowed(&'a B),
    Owned(O),
}
