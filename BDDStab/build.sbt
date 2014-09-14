name := "bdd"

version := "0.1"

scalaVersion := "2.10.3"

libraryDependencies += "com.google.guava" % "guava" % "14.0.1"

libraryDependencies += "com.google.code.findbugs" % "jsr305" % "2.0.1"

resolvers ++= Seq(
  "Sonatype Snapshots" at "http://oss.sonatype.org/content/repositories/snapshots",
  "Sonatype Releases" at "http://oss.sonatype.org/content/repositories/releases"
)

libraryDependencies ++= Seq(
  "org.scalacheck" %% "scalacheck" % "1.11.1" % "test"
)

