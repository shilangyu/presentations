enum LoginState {
    NotLoggedIn,
    Pending(i32),
    LoggedIn { user_id: i32, token: String },
}

fn main() {}
