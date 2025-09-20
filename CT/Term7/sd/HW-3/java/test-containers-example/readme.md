Build app and add docker image with app to local docker registry:

```mvn -am -pl hello-app package```

Run integration test with docker:

```mvn -am -pl test-example test```