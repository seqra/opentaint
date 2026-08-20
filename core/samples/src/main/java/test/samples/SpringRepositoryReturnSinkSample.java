package test.samples;

import org.springframework.data.repository.Repository;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RestController;

@RestController
public final class SpringRepositoryReturnSinkSample {
    private final NoteRepository repository;

    public SpringRepositoryReturnSinkSample(NoteRepository repository) {
        this.repository = repository;
    }

    @GetMapping
    public void update(String text) {
        StoredNote note = repository.findByUuid("id");
        if (note == null) {
            note = new StoredNote();
        }
        note.setText(text);
        repository.save(note);
    }

    @GetMapping
    public String render() {
        StoredNote note = repository.findByUuid("id");
        return note.getText();
    }

    public interface NoteRepository extends Repository<StoredNote, String> {
        StoredNote save(StoredNote note);

        StoredNote findByUuid(String uuid);
    }

    public static final class StoredNote {
        private String text;

        public String getText() {
            return text;
        }

        public void setText(String text) {
            this.text = text;
        }
    }
}
