ThisBuild / version      := "0.1.0-SNAPSHOT"
ThisBuild / scalaVersion := "3.7.3"

lazy val root = (project in file("."))
  .settings(
    name         := "lean2lisa",
    organization := "io.github.yourname",
    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
      "-unchecked",
      "-Wunused:all",
      "-Wsafe-init"
    ),
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.19" % Test,
      "org.scalameta" %% "munit"     % "1.0.0"  % Test
    ),
    Test / parallelExecution := false,
    run / fork               := true,
    run / connectInput       := true
  )
