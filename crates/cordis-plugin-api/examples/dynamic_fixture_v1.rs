mod shared;
fn module() -> cordis_plugin_api::Module {
    shared::module("v1", false)
}
cordis_plugin_api::export_plugin!(module);
