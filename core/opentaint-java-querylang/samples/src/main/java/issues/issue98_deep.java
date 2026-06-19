package issues;

import base.RuleSample;
import base.RuleSet;
import issues.i98.User_i98_deep;

@RuleSet("issues/issue98.yaml")
public abstract class issue98_deep implements RuleSample {
    static class PositiveTaint extends issue98_deep {
        @Override
        public void entrypoint() { (new User_i98_deep()).badUser(); }
    }

    static class PositiveDepth4 extends issue98_deep {
        @Override
        public void entrypoint() { (new User_i98_deep()).badUserDepth4(); }
    }

    static class PositiveDepth3 extends issue98_deep {
        @Override
        public void entrypoint() { (new User_i98_deep()).badUserDepth3(); }
    }

    static class PositiveDepth2 extends issue98_deep {
        @Override
        public void entrypoint() { (new User_i98_deep()).badUserDepth2(); }
    }

    static class PositiveDepth4Call2 extends issue98_deep {
        @Override
        public void entrypoint() { (new User_i98_deep()).badUserDepth4Call2(); }
    }

    static class PositiveDepth4Call3 extends issue98_deep {
        @Override
        public void entrypoint() { (new User_i98_deep()).badUserDepth4Call3(); }
    }
}
