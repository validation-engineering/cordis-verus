mod shared;
fn module() -> cordis_plugin_api::Module {
    shared::module("fail", true)
}
cordis_plugin_api::export_plugin!(module);
