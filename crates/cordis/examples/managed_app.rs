//! Run: cargo run -p cordis-verus --features tokio --example managed_app
use cordis::{App, Plugin, ServiceKey};

#[tokio::main(flavor = "current_thread")]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let app = App::new()?;
    let greeting = ServiceKey::<String>::of();
    let consumer = app
        .plugin(
            Plugin::with_dependencies("consumer", greeting).setup(|_, greeting| {
                println!("{greeting}");
                Ok(())
            }),
        )
        .await?;
    let provider = app
        .plugin(
            Plugin::new("provider", move |ctx| {
                ctx.provide(greeting, "Hello, Cordis".to_owned())?;
                Ok(())
            })
            .provides(greeting),
        )
        .await?;
    consumer.ready().await?;
    provider
        .update_async(move |ctx| async move {
            ctx.provide(greeting, "Hello from the updated provider".to_owned())?;
            Ok(())
        })
        .await?;
    consumer.ready().await?;
    app.shutdown().await?;
    Ok(())
}
