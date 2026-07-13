package security.ldap;


import javax.naming.Context;
import javax.naming.directory.InitialDirContext;
import java.util.Hashtable;

/**
 * Samples for java-anonymous-ldap rule.
 */
public class AnonymousLdapSamples {

    public InitialDirContext anonymousBind(String url) throws Exception {
        Hashtable<String, String> env = new Hashtable<>();
        env.put(Context.INITIAL_CONTEXT_FACTORY, "com.sun.jndi.ldap.LdapCtxFactory");
        env.put(Context.PROVIDER_URL, url);
        // VULNERABLE: explicitly request anonymous authentication
        env.put(Context.SECURITY_AUTHENTICATION, "none");

        return new InitialDirContext(env);
    }

    public InitialDirContext authenticatedBind(String url, String bindDn, String password) throws Exception {
        Hashtable<String, String> env = new Hashtable<>();
        env.put(Context.INITIAL_CONTEXT_FACTORY, "com.sun.jndi.ldap.LdapCtxFactory");
        env.put(Context.PROVIDER_URL, url);
        // SAFE: require simple authentication with credentials
        env.put(Context.SECURITY_AUTHENTICATION, "simple");
        env.put(Context.SECURITY_PRINCIPAL, bindDn);
        env.put(Context.SECURITY_CREDENTIALS, password);

        return new InitialDirContext(env);
    }
}
