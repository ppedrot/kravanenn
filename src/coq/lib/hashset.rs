pub mod combine {
    /// These are helper functions to combine the hash keys in a similar
    /// way as [Hashtbl.hash] does. The constants [alpha] and [beta] must
    /// be prime numbers. There were chosen empirically. Notice that the
    /// problem of hashing trees is hard and there are plenty of study on
    /// this topic. Therefore, there must be room for improvement here.
    const ALPHA : i64 = 65599;
    const BETA : i64 = 7;

    pub const fn combine(x: i64, y: i64) -> i64 {
        // FIXME: Handle overflow.
        x * ALPHA + y
    }

    pub const fn combine3(x: i64, y: i64, z: i64) -> i64 {
        combine(x, combine(y, z))
    }

    pub const fn combine4(x: i64, y: i64, z: i64, t: i64) -> i64 {
        combine(x, combine3(y, z, t))
    }

    pub const fn combine5(x: i64, y: i64, z: i64, t: i64, u: i64) -> i64 {
        combine(x, combine4(y, z, t, u))
    }

    pub const fn combinesmall(x: i64, y: i64) -> i64 {
        // FIXME: Handle overflow.
        BETA * x + y
    }
}
