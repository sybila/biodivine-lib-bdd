//! Contains simple functions that can be used with `apply` and `fused_flip_apply` to
//! implement basic logical operations.

/// Partial operator function corresponding to $x \land y$.
pub fn and(l: Option<bool>, r: Option<bool>) -> Option<bool> {
    match (l, r) {
        (Some(true), Some(true)) => Some(true),
        (Some(false), _) => Some(false),
        (_, Some(false)) => Some(false),
        _ => None,
    }
}

/// Partial operator function corresponding to $x \lor y$.
pub fn or(l: Option<bool>, r: Option<bool>) -> Option<bool> {
    match (l, r) {
        (Some(false), Some(false)) => Some(false),
        (Some(true), _) => Some(true),
        (_, Some(true)) => Some(true),
        _ => None,
    }
}

/// Partial operator function corresponding to $x \Leftarrow y$.
pub fn imp(l: Option<bool>, r: Option<bool>) -> Option<bool> {
    match (l, r) {
        (Some(true), Some(false)) => Some(false),
        (Some(false), _) => Some(true),
        (_, Some(true)) => Some(true),
        _ => None,
    }
}

/// Partial operator function corresponding to $x \Leftrightarrow y$.
pub fn iff(l: Option<bool>, r: Option<bool>) -> Option<bool> {
    match (l, r) {
        (Some(l), Some(r)) => Some(l == r),
        _ => None,
    }
}

/// Partial operator function corresponding to $x \not\Leftrightarrow y$.
pub fn xor(l: Option<bool>, r: Option<bool>) -> Option<bool> {
    match (l, r) {
        (Some(l), Some(r)) => Some(l ^ r),
        _ => None,
    }
}

/// Partial operator function corresponding to $x \land \neg y$.
pub fn and_not(l: Option<bool>, r: Option<bool>) -> Option<bool> {
    match (l, r) {
        (Some(false), _) => Some(false),
        (_, Some(true)) => Some(false),
        (Some(true), Some(false)) => Some(true),
        _ => None,
    }
}
