Java.perform(function () {
    var Application = Java.use("android.app.Application");

    Application.attach.overload("android.content.Context")
        .implementation = function (ctx) {

            //真实入口加载
            console.log("Application attach -> " + this.$className);

            return this.attach(ctx);
        };

});