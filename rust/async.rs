async fn find_user(id: i32) -> String {
    let user = /* Look up in db */ id.to_string();

    return user;
}

#[tokio::main]
async fn main() {
    let user = find_user(123).await.to_uppercase();
}
