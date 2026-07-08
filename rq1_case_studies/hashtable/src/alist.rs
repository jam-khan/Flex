flux_rs::defs! {
    opaque sort ASeq<K, T>;
    fn aseq_cons<K,T>(k: K, t: T, l: ASeq<K, T>) -> ASeq<K, T>;
    fn aseq_nil<K, T>() -> ASeq<K, T>;
    fn aseq_set<K, T>(l: ASeq<K, T>, k: K, v: T) -> ASeq<K, T>;
    fn aseq_remove_key<K, T>(l: ASeq<K, T>, k: K) -> ASeq<K, T>;
    fn aseq_contains_key<K, T>(l: ASeq<K, T>, k: K) -> bool;
    fn aseq_key_matches<K,T>(l: ASeq<K, T>, k: K, v: T) -> bool;
    fn aseq_len<K,T>(l: ASeq<K, T>) -> int;
    fn aseq_unique_keys<K,T>(l: ASeq<K, T>) -> bool;
    fn aseq_keys_unchanged_except_k<K, T>(l1: ASeq<K, T>, l2: ASeq<K, T>, k: K) -> bool;
}

#[flux_rs::refined_by(k: K, v: V)]
pub struct Assoc<K, V> {
    #[flux_rs::field(K[k])]
    pub key: K,
    #[flux_rs::field(V[v])]
    pub val: V,
}

/// Associative list
#[flux_rs::opaque]
#[flux_rs::refined_by(elems: ASeq<K, T>)]
pub enum AList<T, K = usize> {
    #[flux_rs::variant((K[@k], T[@t], Box<AList<T, K>[@l]>) -> AList<T, K>[aseq_cons(k, t, l)])]
    Cons(K, T, Box<AList<T, K>>),
    #[flux_rs::variant(AList<T, K>[aseq_nil()])]
    Nil,
}

impl<T> AList<T> {
    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(Self[@slf], usize[@k], T[@v]) -> (Self[#new_slf], Option<(usize[k], T[v])>[#is_some])
        ensures is_some  == !aseq_contains_key(slf, k),
                is_some  => new_slf == slf,
                !is_some => new_slf == aseq_set(slf, k, v),
    )]
    pub fn replace_if_present(self, k: usize, v: T) -> (Self, Option<(usize, T)>) {
        match self {
            Self::Nil => (Self::Nil, Some((k, v))),
            Self::Cons(ck, _, tl) if ck == k => {
                (Self::Cons(ck, v, tl), None)
            }
            Self::Cons(ck, cv, tl) => {
                let (rest, replaced) = tl.replace_if_present(k, v);
                (Self::Cons(ck, cv, Box::new(rest)), replaced)
            }
        }
    }
}