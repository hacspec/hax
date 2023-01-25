module.exports = function override(config, env) {
    //do stuff with the webpack config...
    config.minimize = false;
    return config;
}
